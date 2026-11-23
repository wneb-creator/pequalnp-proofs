import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Normalization

open Turing

noncomputable def allStmts (tm : FinTM2) : Finset tm.Stmt := by
  classical
  let := tm.ΛFin
  exact Finset.univ.biUnion fun l : tm.Λ => TM2.stmts₁ (tm.m l)

def Node (tm : FinTM2) := {q : tm.Stmt // q ∈ allStmts tm}

lemma root_mem (tm : FinTM2) (l : tm.Λ) : tm.m l ∈ allStmts tm := by
  classical
  let := tm.ΛFin
  change tm.m l ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z))
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, TM2.stmts₁_self⟩

lemma child_mem (tm : FinTM2) (q : Node tm) (r : tm.Stmt)
    (hr : r ∈ TM2.stmts₁ q.val) : r ∈ allStmts tm := by
  classical
  let := tm.ΛFin
  have hq := q.property
  change q.val ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z)) at hq
  change r ∈ Finset.univ.biUnion (fun z : tm.Λ => TM2.stmts₁ (tm.m z))
  rcases Finset.mem_biUnion.mp hq with ⟨l, hl, hq⟩
  exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_trans hq hr⟩

noncomputable def root (tm : FinTM2) (l : tm.Λ) : Node tm := ⟨tm.m l, root_mem tm l⟩

noncomputable def child (tm : FinTM2) (q : Node tm) (r : tm.Stmt)
    (hr : r ∈ TM2.stmts₁ q.val) : Node tm := ⟨r, child_mem tm q r hr⟩

noncomputable def code (tm : FinTM2) (q : Node tm) : TM2.Stmt tm.Γ (Node tm) tm.σ := by
  classical
  cases h : q.val with
  | push k f r =>
      exact .push k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | peek k f r =>
      exact .peek k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | pop k f r =>
      exact .pop k f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | load f r =>
      exact .load f (.goto fun _ => child tm q r (by rw [h]; exact Finset.mem_insert_of_mem TM2.stmts₁_self))
  | branch f r s =>
      exact .goto fun v => if f v then
        child tm q r (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
        else child tm q s (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
  | goto f => exact .goto fun v => root tm (f v)
  | halt => exact .halt

noncomputable def normalized (tm : FinTM2) : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := tm.Γ
  Λ := Node tm
  main := root tm tm.main
  ΛFin := by unfold Node; infer_instance
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := tm.Γk₀Fin
  m := code tm

noncomputable def liftCfg (tm : FinTM2) (cfg : tm.Cfg) : (normalized tm).Cfg :=
  ⟨cfg.l.map (root tm), cfg.var, cfg.stk⟩

lemma liftCfg_init (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    liftCfg tm (Turing.initList tm input) = Turing.initList (normalized tm) input := by
  rfl

lemma liftCfg_halt (tm : FinTM2) (output : List (tm.Γ tm.k₁)) :
    liftCfg tm (Turing.haltList tm output) = Turing.haltList (normalized tm) output := by
  rfl

def depth {K : Type*} {Γ : K → Type*} {Λ σ : Type*} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q + 1
  | .branch _ q r => depth q + depth r + 1
  | .goto _ => 1
  | .halt => 1

def oneStep {α : Type*} (f : α → Option α) (a b : α) (h : f a = some b) :
    StateTransition.EvalsToInTime f a (some b) 1 :=
  ⟨⟨1, by change f a = some b; exact h⟩, le_rfl⟩

def widenTime {α : Type*} {f : α → Option α} {a : α} {b : Option α} {m n : ℕ}
    (h : StateTransition.EvalsToInTime f a b m) (hmn : m ≤ n) :
    StateTransition.EvalsToInTime f a b n :=
  { h with steps_le_m := h.steps_le_m.trans hmn }

lemma simulate_statement (tm : FinTM2) (q : tm.Stmt) (hq : q ∈ allStmts tm)
    (v : tm.σ) (stk : ∀ k, List (tm.Γ k)) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      ⟨some ⟨q, hq⟩, v, stk⟩ (some (liftCfg tm (TM2.stepAux q v stk))) (depth q)) := by
  classical
  induction q generalizing v stk with
  | push k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.push k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr v (Function.update stk k (f v :: stk k))
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | peek k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.peek k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v (stk k).head?) stk
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | pop k f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.pop k f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v (stk k).head?) (Function.update stk k (stk k).tail)
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | load f r ih =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.load f r, hq⟩ r
        (Finset.mem_insert_of_mem TM2.stmts₁_self)
      obtain ⟨rest⟩ := ih hr (f v) stk
      exact ⟨StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
        (oneStep _ _ _ (by rfl)) rest⟩
  | branch f r s ihr ihs =>
      have hr : r ∈ allStmts tm := child_mem tm ⟨.branch f r s, hq⟩ r
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      have hs : s ∈ allStmts tm := child_mem tm ⟨.branch f r s, hq⟩ s
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      cases hv : f v
      · obtain ⟨rest⟩ := ihs hs v stk
        have first : (normalized tm).step ⟨some ⟨.branch f r s, hq⟩, v, stk⟩ =
            some ⟨some ⟨s, hs⟩, v, stk⟩ := by
          simp [normalized, FinTM2.step, TM2.step, code, TM2.stepAux, hv, child]
          rfl
        have total := StateTransition.EvalsToInTime.trans _ 1 (depth s) _ _ _
          (oneStep _ _ _ first) rest
        simp only [TM2.stepAux, hv, Bool.cond_false]
        exact ⟨widenTime total (by dsimp [depth]; omega)⟩
      · obtain ⟨rest⟩ := ihr hr v stk
        have first : (normalized tm).step ⟨some ⟨.branch f r s, hq⟩, v, stk⟩ =
            some ⟨some ⟨r, hr⟩, v, stk⟩ := by
          simp [normalized, FinTM2.step, TM2.step, code, TM2.stepAux, hv, child]
          rfl
        have total := StateTransition.EvalsToInTime.trans _ 1 (depth r) _ _ _
          (oneStep _ _ _ first) rest
        simp only [TM2.stepAux, hv, Bool.cond_true]
        exact ⟨widenTime total (by dsimp [depth]; omega)⟩
  | goto f => exact ⟨oneStep _ _ _ (by rfl)⟩
  | halt => exact ⟨oneStep _ _ _ (by rfl)⟩

noncomputable def bound (tm : FinTM2) : ℕ := by
  let := tm.ΛFin
  exact 1 + ∑ l : tm.Λ, depth (tm.m l)

lemma depth_le_bound (tm : FinTM2) (l : tm.Λ) : depth (tm.m l) ≤ bound tm := by
  let := tm.ΛFin
  have h : depth (tm.m l) ≤ ∑ z : tm.Λ, depth (tm.m z) :=
    Finset.single_le_sum (f := fun z : tm.Λ => depth (tm.m z))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  unfold bound
  dsimp only
  omega

lemma simulate_step (tm : FinTM2) (a b : tm.Cfg) (h : tm.step a = some b) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm)) := by
  cases a with
  | mk label v stk =>
    cases label with
    | none => cases h
    | some l =>
      have hb : TM2.stepAux (tm.m l) v stk = b := Option.some.inj h
      subst b
      obtain ⟨run⟩ := simulate_statement tm (tm.m l) (root_mem tm l) v stk
      exact ⟨widenTime run (depth_le_bound tm l)⟩

lemma iterate_none {α : Type*} (f : α → Option α) (n : ℕ) :
    (fun x : Option α => x.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

lemma simulate_steps (tm : FinTM2) (n : ℕ) (a b : tm.Cfg)
    (h : (fun x : Option tm.Cfg => x.bind tm.step)^[n] (some a) = some b) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm * n)) := by
  induction n generalizing a with
  | zero =>
      have hab : a = b := Option.some.inj h
      subst a
      exact ⟨StateTransition.EvalsToInTime.refl _ _⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      change (fun x : Option tm.Cfg => x.bind tm.step)^[n] (tm.step a) = some b at h
      cases ha : tm.step a with
      | none =>
          rw [ha, iterate_none] at h
          cases h
      | some c =>
          rw [ha] at h
          obtain ⟨rest⟩ := ih c h
          obtain ⟨first⟩ := simulate_step tm a c ha
          have total := StateTransition.EvalsToInTime.trans _ (bound tm) (bound tm * n)
            _ _ _ first rest
          rw [Nat.mul_succ]
          exact ⟨total⟩

lemma simulate_time (tm : FinTM2) (a b : tm.Cfg) (t : ℕ)
    (h : StateTransition.EvalsToInTime tm.step a (some b) t) :
    Nonempty (StateTransition.EvalsToInTime (normalized tm).step
      (liftCfg tm a) (some (liftCfg tm b)) (bound tm * t)) := by
  obtain ⟨run⟩ := simulate_steps tm h.steps a b h.evals_in_steps
  exact ⟨widenTime run (Nat.mul_le_mul_left _ h.steps_le_m)⟩

noncomputable def normalizedComputation {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (c : Turing.TM2ComputableInTime ea eb f) : Turing.TM2ComputableInTime ea eb f where
  tm := normalized c.tm
  inputAlphabet := c.inputAlphabet
  outputAlphabet := c.outputAlphabet
  time n := bound c.tm * c.time n
  outputsFun a := Classical.choice (simulate_time c.tm _ _ _ (c.outputsFun a))

lemma normalized_code_depth (tm : FinTM2) (q : Node tm) : depth (code tm q) ≤ 2 := by
  classical
  rcases q with ⟨q, hq⟩
  cases q <;> simp [code, depth]

end PEqualNP.Outside.Normalization
