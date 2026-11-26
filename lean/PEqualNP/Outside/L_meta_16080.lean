import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16080

section
namespace MachNS

open Turing

theorem iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem simulate {σ τ : Type} (f : σ → Option σ) (g : τ → Option τ) (emb : σ → τ)
    (h : ∀ c c', f c = some c' → g (emb c) = some (emb c')) :
    ∀ (n : ℕ) (a b : σ), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (emb a)) = some (emb b) := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; rfl
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab ⊢
    cases hfa : f a with
    | none =>
      have e : flip bind f (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind f (some a) = some c := hfa
      have e' : flip bind g (some (emb a)) = some (emb c) := h a c hfa
      rw [e] at hab
      rw [e']
      exact ih c b hab

section pushes

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_cons]; omega
    · rw [Function.update_of_ne h]; omega
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
    simp only [TM2.stepAux, pushes]
    refine (ih _ _).trans ?_
    by_cases h : k = k'
    · subst h
      rw [Function.update_self, List.length_tail]; omega
    · rw [Function.update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by have := le_max_right (pushes q₁) (pushes q₂); omega)
    · exact (ih₁ v S).trans (by have := le_max_left (pushes q₁) (pushes q₂); omega)
  | goto f => simp [TM2.stepAux, pushes]
  | halt => simp [TM2.stepAux, pushes]

end pushes

noncomputable def maxPush (tm : FinTM2) : ℕ :=
  (@Finset.univ tm.Λ tm.ΛFin).sup fun l => pushes (tm.m l)

theorem step_length (tm : FinTM2) (c c' : TM2.Cfg tm.Γ tm.Λ tm.σ)
    (h : TM2.step tm.m c = some c') (k : tm.K) :
    (c'.stk k).length ≤ (c.stk k).length + maxPush tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    refine (stepAux_length _ _ _ _).trans ?_
    have : pushes (tm.m l) ≤ maxPush tm :=
      Finset.le_sup (f := fun l => pushes (tm.m l)) (@Finset.mem_univ tm.Λ tm.ΛFin l)
    simpa using this

theorem run_length (tm : FinTM2) (k : tm.K) :
    ∀ (n : ℕ) (a b : TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind (TM2.step tm.m))^[n] (some a) = some b →
      (b.stk k).length ≤ (a.stk k).length + maxPush tm * n := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    have : a = b := Option.some.inj hab
    rw [this]; simp
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step tm.m a with
    | none =>
      have e : flip bind (TM2.step tm.m) (some a) = none := hfa
      rw [e, iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step tm.m) (some a) = some c := hfa
      rw [e] at hab
      have h1 := ih c b hab
      have h2 := step_length tm a c hfa k
      rw [Nat.mul_succ]; omega

theorem initList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main, tm.initialState, Function.update (fun _ => []) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold initList
  congr 1
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

theorem haltList_eq (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList
  congr 1
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · simp [h]

theorem eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial d c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

end MachNS
end

section
open Turing

namespace EnumNS

section tr

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  {K' : Type} [DecidableEq K'] {G Λ' σ' : Type}
  (eK : K ≃ K') (eΛ : Λ → Λ') (eσ : σ ≃ σ') (π : (Σ k, Γ k) → G) (ι : ∀ k, G → Option (Γ k))

def tr : TM2.Stmt Γ Λ σ → TM2.Stmt (fun _ : K' => G) Λ' σ'
  | .push k f q => .push (eK k) (fun v => π ⟨k, f (eσ.symm v)⟩) (tr q)
  | .peek k f q => .peek (eK k) (fun v o => eσ (f (eσ.symm v) (o.bind (ι k)))) (tr q)
  | .pop k f q => .pop (eK k) (fun v o => eσ (f (eσ.symm v) (o.bind (ι k)))) (tr q)
  | .load a q => .load (fun v => eσ (a (eσ.symm v))) (tr q)
  | .branch f q₁ q₂ => .branch (fun v => f (eσ.symm v)) (tr q₁) (tr q₂)
  | .goto f => .goto (fun v => eΛ (f (eσ.symm v)))
  | .halt => .halt

def mapS (S : ∀ k, List (Γ k)) : K' → List G :=
  fun k' => (S (eK.symm k')).map (fun s => π ⟨eK.symm k', s⟩)

def mapC (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K' => G) Λ' σ' :=
  ⟨c.l.map eΛ, eσ c.var, mapS eK π c.stk⟩

def pushSet : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ pushSet q
  | .peek _ _ q => pushSet q
  | .pop _ _ q => pushSet q
  | .load _ q => pushSet q
  | .branch _ q₁ q₂ => pushSet q₁ ∪ pushSet q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushSet_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (pushSet q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

def Good (T : Set (Σ k, Γ k)) (S : ∀ k, List (Γ k)) : Prop :=
  ∀ k, ∀ s ∈ S k, (⟨k, s⟩ : Σ k, Γ k) ∈ T

theorem mapS_apply (S : ∀ k, List (Γ k)) (k : K) :
    mapS eK π S (eK k) = (S k).map (fun s => π ⟨k, s⟩) := by
  unfold mapS
  rw [Equiv.symm_apply_apply]

theorem mapS_update (S : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    mapS eK π (Function.update S k l) =
      Function.update (mapS eK π S) (eK k) (l.map (fun s => π ⟨k, s⟩)) := by
  funext k'
  obtain ⟨j, rfl⟩ := eK.surjective k'
  rw [mapS_apply]
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne (eK.injective.ne h), mapS_apply]

theorem mapS_empty : mapS eK π (fun _ => ([] : List (Γ _))) = fun _ => [] := rfl

variable {π ι} (T : Set (Σ k, Γ k))

theorem good_update {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) (l : List (Γ k))
    (hl : ∀ s ∈ l, (⟨k, s⟩ : Σ k, Γ k) ∈ T) : Good T (Function.update S k l) := by
  intro j s hs
  by_cases h : j = k
  · subst h; rw [Function.update_self] at hs; exact hl s hs
  · rw [Function.update_of_ne h] at hs; exact hS j s hs

theorem head_bind (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) :
    ((mapS eK π S (eK k)).head?).bind (ι k) = (S k).head? := by
  rw [mapS_apply]
  have hk := hS k
  cases h : S k with
  | nil => rfl
  | cons s r =>
    rw [h] at hk
    simp only [List.map_cons, List.head?_cons, Option.bind_some]
    exact hι k s (hk s (by simp))

theorem stepAux_tr (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    (q : TM2.Stmt Γ Λ σ) (hq : pushSet q ⊆ T) (v : σ) (S : ∀ k, List (Γ k)) (hS : Good T S) :
    TM2.stepAux (tr eK eΛ eσ π ι q) (eσ v) (mapS eK π S) = mapC eK eΛ eσ π (TM2.stepAux q v S) ∧
      Good T (TM2.stepAux q v S).stk := by
  induction q generalizing v S with
  | push k f q ih =>
    have hq' : pushSet q ⊆ T := fun x hx => hq (Or.inr hx)
    have hf : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
    have hS' : Good T (Function.update S k (f v :: S k)) := by
      refine good_update T hS k _ (fun s hs => ?_)
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hf
      · exact hS k s hs
    have e : Function.update (mapS eK π S) (eK k) (π ⟨k, f (eσ.symm (eσ v))⟩ :: mapS eK π S (eK k))
        = mapS eK π (Function.update S k (f v :: S k)) := by
      rw [mapS_update, mapS_apply, Equiv.symm_apply_apply, List.map_cons]
    simp only [tr, TM2.stepAux]
    rw [e]
    exact ih hq' v _ hS'
  | peek k f q ih =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply, head_bind eK T hι hS k]
    exact ih hq _ S hS
  | pop k f q ih =>
    have hS' : Good T (Function.update S k (S k).tail) :=
      good_update T hS k _ (fun s hs => hS k s (List.mem_of_mem_tail hs))
    have e : Function.update (mapS eK π S) (eK k) (mapS eK π S (eK k)).tail
        = mapS eK π (Function.update S k (S k).tail) := by
      rw [mapS_update, mapS_apply, List.map_tail]
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply, head_bind eK T hι hS k, e]
    exact ih hq _ _ hS'
  | load a q ih =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply]
    exact ih hq _ S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [tr, TM2.stepAux]
    rw [Equiv.symm_apply_apply]
    cases f v
    · exact ih₂ (fun x hx => hq (Or.inr hx)) v S hS
    · exact ih₁ (fun x hx => hq (Or.inl hx)) v S hS
  | goto f =>
    simp only [tr, TM2.stepAux, Equiv.symm_apply_apply]
    exact ⟨rfl, hS⟩
  | halt =>
    simp only [tr, TM2.stepAux]
    exact ⟨rfl, hS⟩

theorem mapC_inj (hι : ∀ k s, (⟨k, s⟩ : Σ k, Γ k) ∈ T → ι k (π ⟨k, s⟩) = some s)
    (heΛ : Function.Injective eΛ) {c c' : TM2.Cfg Γ Λ σ} (hc : Good T c.stk)
    (hc' : Good T c'.stk) (h : mapC eK eΛ eσ π c = mapC eK eΛ eσ π c') : c = c' := by
  obtain ⟨l, v, S⟩ := c
  obtain ⟨l', v', S'⟩ := c'
  simp only [mapC, TM2.Cfg.mk.injEq] at h
  obtain ⟨hl, hv, hS⟩ := h
  have hl' : l = l' := Option.map_injective heΛ hl
  have hv' : v = v' := eσ.injective hv
  subst hl' hv'
  have hS' : S = S' := by
    funext k
    have e := congrFun hS (eK k)
    rw [mapS_apply, mapS_apply] at e
    have e2 := congrArg (List.map (ι k)) e
    rw [List.map_map, List.map_map] at e2
    have r1 : (S k).map (ι k ∘ fun s => π ⟨k, s⟩) = (S k).map some :=
      List.map_congr_left (fun s hs => hι k s (hc k s hs))
    have r2 : (S' k).map (ι k ∘ fun s => π ⟨k, s⟩) = (S' k).map some :=
      List.map_congr_left (fun s hs => hι k s (hc' k s hs))
    rw [r1, r2] at e2
    exact List.map_injective_iff.mpr (Option.some_injective _) e2
  rw [hS']

end tr

end EnumNS
end

section
namespace TabNS

open PEqualNP.CircuitLowerBounds

inductive Ex (α : Type) where
  | var : α → Ex α
  | const : Bool → Ex α
  | not : Ex α → Ex α
  | and : Ex α → Ex α → Ex α
  | or : Ex α → Ex α → Ex α

namespace Ex

variable {α β : Type}

def eval (ρ : α → Bool) : Ex α → Bool
  | var a => ρ a
  | const b => b
  | not e => !(eval ρ e)
  | and e f => eval ρ e && eval ρ f
  | or e f => eval ρ e || eval ρ f

def size : Ex α → ℕ
  | var _ => 1
  | const _ => 1
  | not e => size e + 1
  | and e f => size e + size f + 1
  | or e f => size e + size f + 1

def bind (σ : α → Ex β) : Ex α → Ex β
  | var a => σ a
  | const b => const b
  | not e => not (bind σ e)
  | and e f => and (bind σ e) (bind σ f)
  | or e f => or (bind σ e) (bind σ f)

theorem eval_bind (ρ : β → Bool) (σ : α → Ex β) (e : Ex α) :
    eval ρ (bind σ e) = eval (fun a => eval ρ (σ a)) e := by
  induction e with
  | var a => rfl
  | const b => rfl
  | not e ih => simp [bind, eval, ih]
  | and e f ih1 ih2 => simp [bind, eval, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, eval, ih1, ih2]

theorem size_bind (σ : α → Ex β) (hσ : ∀ a, size (σ a) = 1) (e : Ex α) :
    size (bind σ e) = size e := by
  induction e with
  | var a => exact hσ a
  | const b => rfl
  | not e ih => simp [bind, size, ih]
  | and e f ih1 ih2 => simp [bind, size, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, size, ih1, ih2]

end Ex

open Ex

def run (gs : List Gate) (W : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W

theorem run_wires (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_nil (W : List Bool) : run [] W = W := rfl

theorem run_single (g : Gate) (W : List Bool) :
    run [g] W = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := rfl

theorem run_prefix (gs : List Gate) : ∀ W : List Bool, ∃ t, run gs W = W ++ t := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t, ?_⟩
    change run gs _ = _
    rw [ht, List.append_assoc]

theorem length_run (gs : List Gate) : ∀ W : List Bool, (run gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp [run]
  | cons g gs ih =>
    intro W
    change (run gs _).length = _
    rw [ih]; simp; omega

theorem getD_run (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht⟩ := run_prefix gs W
  rw [ht, List.getD_append _ _ _ _ h]

def Rep {α : Type} (W : List Bool) (w : α → ℕ) (ρ : α → Bool) : Prop :=
  ∀ a, w a < W.length ∧ W.getD (w a) false = ρ a

theorem rep_run {α : Type} {W : List Bool} {w : α → ℕ} {ρ : α → Bool} (h : Rep W w ρ)
    (gs : List Gate) : Rep (run gs W) w ρ := by
  intro a
  refine ⟨?_, ?_⟩
  · rw [length_run]; have := (h a).1; omega
  · rw [getD_run _ _ _ (h a).1]; exact (h a).2

def Basic (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

section compile

variable {α : Type} (w : α → ℕ)

def compile : Ex α → ℕ → List Gate × ℕ
  | .var a, _ => ([], w a)
  | .const b, N => ([⟨if b then GateOp.and else GateOp.or, []⟩], N)
  | .not e, N =>
    let p := compile e N
    (p.1 ++ [⟨GateOp.not, [p.2]⟩], N + p.1.length)
  | .and e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.and, [p.2, q.2]⟩], N + p.1.length + q.1.length)
  | .or e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.or, [p.2, q.2]⟩], N + p.1.length + q.1.length)

theorem compile_basic : ∀ (e : Ex α) (N : ℕ), ∀ g ∈ (compile w e N).1, Basic g
  | .var a, N => by simp [compile]
  | .const b, N => by
    intro g hg
    simp only [compile, List.mem_singleton] at hg
    subst hg
    cases b <;> simp [Basic]
  | .not e, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact compile_basic e N g hg
    · subst hg; simp [Basic]
  | .and e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]
  | .or e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]

theorem compile_length : ∀ (e : Ex α) (N : ℕ), (compile w e N).1.length ≤ size e
  | .var a, N => by simp [compile, size]
  | .const b, N => by simp [compile, size]
  | .not e, N => by
    have := compile_length e N
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .and e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .or e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega

theorem getD_snoc_len (W : List Bool) (b : Bool) : (W ++ [b]).getD W.length false = b := by
  simp

theorem compile_spec : ∀ (e : Ex α) (W : List Bool) (ρ : α → Bool), Rep W w ρ →
    (compile w e W.length).2 < W.length + (compile w e W.length).1.length ∧
    (run (compile w e W.length).1 W).getD (compile w e W.length).2 false = eval ρ e
  | .var a, W, ρ, h => by
    simp only [compile, List.length_nil, Nat.add_zero, run_nil, eval]
    exact h a
  | .const b, W, ρ, h => by
    simp only [compile, List.length_singleton, run_single, eval]
    refine ⟨by omega, ?_⟩
    rw [getD_snoc_len]
    cases b <;> simp [GateOp.eval]
  | .not e, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    have hl := length_run (compile w e W.length).1 W
    rw [← hl, getD_snoc_len]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    exact congrArg _ h2
  | .and e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    exact congrArg₂ _ e2 h4
  | .or e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    exact congrArg₂ _ e2 h4

end compile

def Sim {α β : Type} (F : (α → Bool) → (β → Bool)) (s : ℕ) : Prop :=
  ∀ (N : ℕ) (w : α → ℕ), ∃ (gs : List Gate) (w' : β → ℕ), (∀ g ∈ gs, Basic g) ∧
    gs.length ≤ s ∧ ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
      Rep (run gs W) w' (F ρ)

theorem sim_mono {α β : Type} {F : (α → Bool) → (β → Bool)} {s t : ℕ} (h : Sim F s)
    (hst : s ≤ t) : Sim F t := by
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := h N w
  exact ⟨gs, w', h1, h2.trans hst, h3⟩

theorem sim_id {α : Type} : Sim (fun ρ : α → Bool => ρ) 0 := by
  intro N w
  exact ⟨[], w, by simp, by simp, fun W ρ _ h => h⟩

theorem sim_comp {α β γ : Type} {F : (α → Bool) → (β → Bool)} {G : (β → Bool) → (γ → Bool)}
    {s t : ℕ} (hF : Sim F s) (hG : Sim G t) : Sim (fun ρ => G (F ρ)) (s + t) := by
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := hF N w
  obtain ⟨gs', w'', h1', h2', h3'⟩ := hG (N + gs.length) w'
  refine ⟨gs ++ gs', w'', ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · exact h1' g hg
  · rw [List.length_append]; omega
  · intro W ρ hW hR
    rw [run_append]
    exact h3' _ _ (by rw [length_run, hW]) (h3 W ρ hW hR)

theorem sim_iter {α : Type} {F : (α → Bool) → (α → Bool)} {s : ℕ} (hF : Sim F s) :
    ∀ k : ℕ, Sim (F^[k]) (k * s) := by
  intro k
  induction k with
  | zero => rw [Nat.zero_mul]; exact sim_id
  | succ k ih =>
    have := sim_comp hF ih
    refine sim_mono ?_ (by rw [Nat.succ_mul, Nat.add_comm])
    rw [Function.iterate_succ]; exact this

theorem sim_layer_list {α β : Type} (e : β → Ex α) (l : List β) (N : ℕ) (w : α → ℕ) :
    ∃ (gs : List Gate) (w' : β → ℕ), (∀ g ∈ gs, Basic g) ∧
      gs.length ≤ (l.map fun b => size (e b)).sum ∧
      ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
        ∀ b ∈ l, w' b < (run gs W).length ∧ (run gs W).getD (w' b) false = eval ρ (e b) := by
  classical
  induction l generalizing N with
  | nil => exact ⟨[], fun _ => 0, by simp, by simp, fun W ρ _ _ b hb => by simp at hb⟩
  | cons b l ih =>
    have c0 := compile_basic w (e b) N
    have cL := compile_length w (e b) N
    have cS : ∀ (W : List Bool) (ρ : α → Bool), W.length = N → Rep W w ρ →
        (compile w (e b) N).2 < N + (compile w (e b) N).1.length ∧
        (run (compile w (e b) N).1 W).getD (compile w (e b) N).2 false = eval ρ (e b) := by
      intro W ρ hW hR; subst hW; exact compile_spec w (e b) W ρ hR
    generalize compile w (e b) N = p at c0 cL cS
    obtain ⟨gs, w', h1, h2, h3⟩ := ih (N + p.1.length)
    refine ⟨p.1 ++ gs, fun b' => if b' = b then p.2 else w' b', ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact c0 g hg
      · exact h1 g hg
    · simp only [List.length_append, List.map_cons, List.sum_cons]; omega
    · intro W ρ hW hR b' hb'
      rw [run_append]
      have hl := length_run p.1 W
      have hR' := rep_run hR p.1
      by_cases hbb : b' = b
      · subst hbb
        simp only [ite_true]
        obtain ⟨c1, c2⟩ := cS W ρ hW hR
        refine ⟨?_, ?_⟩
        · rw [length_run, hl]; omega
        · rw [getD_run _ _ _ (by rw [hl]; omega)]; exact c2
      · simp only [hbb, ite_false]
        have hb'' : b' ∈ l := by
          rcases List.mem_cons.1 hb' with h | h
          · exact absurd h hbb
          · exact h
        exact h3 (run p.1 W) ρ (by rw [hl, hW]) hR' b' hb''

theorem sim_layer {α β : Type} [Fintype β] (e : β → Ex α) :
    Sim (fun ρ b => eval ρ (e b)) (∑ b, size (e b)) := by
  classical
  intro N w
  obtain ⟨gs, w', h1, h2, h3⟩ := sim_layer_list e Finset.univ.toList N w
  refine ⟨gs, w', h1, ?_, ?_⟩
  · refine h2.trans (le_of_eq ?_)
    rw [Finset.sum_map_toList]
  · intro W ρ hW hR b
    exact h3 W ρ hW hR b (Finset.mem_toList.2 (Finset.mem_univ b))

theorem exists_ex_fin : ∀ (k : ℕ) (f : (Fin k → Bool) → Bool),
    ∃ E : Ex (Fin k), size E + 6 ≤ 7 * 2 ^ k ∧ ∀ ρ, eval ρ E = f ρ
  | 0, f => ⟨Ex.const (f fun i => i.elim0), by simp [size], fun ρ => by
      simp only [eval]; congr 1; funext i; exact i.elim0⟩
  | k + 1, f => by
    obtain ⟨E1, s1, e1⟩ := exists_ex_fin k (fun τ => f (Fin.snoc τ true))
    obtain ⟨E0, s0, e0⟩ := exists_ex_fin k (fun τ => f (Fin.snoc τ false))
    let σ : Fin k → Ex (Fin (k + 1)) := fun i => Ex.var i.castSucc
    have hσ : ∀ i, size (σ i) = 1 := fun i => rfl
    refine ⟨Ex.or (Ex.and (Ex.var (Fin.last k)) (bind σ E1))
      (Ex.and (Ex.not (Ex.var (Fin.last k))) (bind σ E0)),
      ?_, ?_⟩
    · simp only [size, size_bind σ hσ]; rw [pow_succ]; omega
    · intro ρ
      simp only [eval, eval_bind, σ, e1, e0]
      have h := Fin.snoc_init_self ρ
      cases hl : ρ (Fin.last k)
      · simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
        conv_rhs => rw [← h, hl]
        rfl
      · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
        conv_rhs => rw [← h, hl]
        rfl

theorem exists_ex {V : Type} [Fintype V] (f : (V → Bool) → Bool) :
    ∃ E : Ex V, size E + 6 ≤ 7 * 2 ^ Fintype.card V ∧ ∀ ρ, eval ρ E = f ρ := by
  let e := Fintype.equivFin V
  obtain ⟨E, s, h⟩ := exists_ex_fin (Fintype.card V) (fun τ => f (fun v => τ (e v)))
  let σ : Fin (Fintype.card V) → Ex V := fun i => Ex.var (e.symm i)
  refine ⟨bind σ E, by rw [size_bind σ (fun _ => rfl)]; exact s, fun ρ => ?_⟩
  rw [eval_bind, h]
  simp [σ, eval]

theorem exists_ex_det {X V : Type} [Fintype V] (enc : X → V → Bool) (P : X → Prop)
    (f : X → Bool) (hdet : ∀ x y, P x → P y → enc x = enc y → f x = f y) :
    ∃ E : Ex V, size E + 6 ≤ 7 * 2 ^ Fintype.card V ∧ ∀ x, P x → eval (enc x) E = f x := by
  classical
  let F : (V → Bool) → Bool := fun b => if h : ∃ x, P x ∧ enc x = b then f h.choose else false
  obtain ⟨E, s, h⟩ := exists_ex F
  refine ⟨E, s, fun x hx => ?_⟩
  rw [h]
  have hex : ∃ y, P y ∧ enc y = enc x := ⟨x, hx, rfl⟩
  simp only [F, hex]
  exact hdet _ _ hex.choose_spec.1 hx hex.choose_spec.2

end TabNS
end

section
open Turing

namespace TabNS

section stmt

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def pops : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pops q
  | .peek _ _ q => pops q + 1
  | .pop _ _ q => pops q + 1
  | .load _ q => pops q
  | .branch _ q₁ q₂ => max (pops q₁) (pops q₂)
  | .goto _ => 0
  | .halt => 0

theorem update_append (P R : ∀ k, List (Γ k)) (k : K) (l : List (Γ k)) :
    Function.update (fun k => P k ++ R k) k (l ++ R k) =
      fun k' => Function.update P k l k' ++ R k' := by
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem head_append_of (P R : List α) (h : 1 ≤ P.length ∨ R = []) :
    (P ++ R).head? = P.head? := by
  rcases h with h | h
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · subst h; simp

theorem tail_append_of (P R : List α) (h : 1 ≤ P.length ∨ R = []) :
    (P ++ R).tail = P.tail ++ R := by
  rcases h with h | h
  · cases P with
    | nil => simp at h
    | cons a P => rfl
  · subst h; simp

theorem stepAux_split (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (P R : ∀ k, List (Γ k)),
    (∀ k, pops q ≤ (P k).length ∨ R k = []) →
    TM2.stepAux q v (fun k => P k ++ R k) =
      ⟨(TM2.stepAux q v P).l, (TM2.stepAux q v P).var,
        fun k => (TM2.stepAux q v P).stk k ++ R k⟩ := by
  induction q with
  | push k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have e : Function.update (fun k => P k ++ R k) k (f v :: (P k ++ R k)) =
        fun k' => Function.update P k (f v :: P k) k' ++ R k' := by
      rw [← update_append]; rfl
    rw [e]
    apply ih
    intro k'
    rcases h k' with h | h
    · left
      by_cases hk : k' = k
      · subst hk; simp only [Function.update_self, List.length_cons]; simp only [pops] at h; omega
      · rw [Function.update_of_ne hk]; exact h
    · right; exact h
  | peek k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have e : (P k ++ R k).head? = (P k).head? := by
      apply head_append_of
      rcases h k with h | h
      · left; simp only [pops] at h; omega
      · right; exact h
    rw [e]
    apply ih
    intro k'
    rcases h k' with h | h
    · left; simp only [pops] at h; omega
    · right; exact h
  | pop k f q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    have h1 : 1 ≤ (P k).length ∨ R k = [] := by
      rcases h k with h | h
      · left; simp only [pops] at h; omega
      · right; exact h
    rw [head_append_of _ _ h1, tail_append_of _ _ h1, update_append]
    apply ih
    intro k'
    rcases h k' with h | h
    · left
      by_cases hk : k' = k
      · subst hk; simp only [Function.update_self, List.length_tail]; simp only [pops] at h
        omega
      · rw [Function.update_of_ne hk]; simp only [pops] at h; omega
    · right; exact h
  | load a q ih =>
    intro v P R h
    simp only [TM2.stepAux]
    exact ih _ P R (fun k => by simpa [pops] using h k)
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v P R h
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ v P R (fun k => by
        rcases h k with h | h
        · left; simp only [pops] at h; omega
        · right; exact h)
    · exact ih₁ v P R (fun k => by
        rcases h k with h | h
        · left; simp only [pops] at h; omega
        · right; exact h)
  | goto f => intro v P R h; rfl
  | halt => intro v P R h; rfl

theorem stepAux_take (q : TM2.Stmt Γ Λ σ) (d : ℕ) (hd : pops q ≤ d) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.stepAux q v S =
      ⟨(TM2.stepAux q v (fun k => (S k).take d)).l,
        (TM2.stepAux q v (fun k => (S k).take d)).var,
        fun k => (TM2.stepAux q v (fun k => (S k).take d)).stk k ++ (S k).drop d⟩ := by
  have e : S = fun k => (S k).take d ++ (S k).drop d := by
    funext k; simp
  conv_lhs => rw [e]
  apply stepAux_split
  intro k
  by_cases h : d ≤ (S k).length
  · left; rw [List.length_take]; omega
  · right; rw [List.drop_eq_nil_iff]; omega

open EnumNS in
theorem good_stepAux (T : Set (Σ k, Γ k)) (q : TM2.Stmt Γ Λ σ) (hq : pushSet q ⊆ T) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)), Good T S → Good T (TM2.stepAux q v S).stk := by
  induction q with
  | push k f q ih =>
    intro v S hS
    simp only [TM2.stepAux]
    apply ih (fun x hx => hq (Or.inr hx))
    intro k' s hs
    by_cases hk : k' = k
    · subst hk
      rw [Function.update_self] at hs
      rcases List.mem_cons.1 hs with hs | hs
      · subst hs; exact hq (Or.inl ⟨v, rfl⟩)
      · exact hS k' s hs
    · rw [Function.update_of_ne hk] at hs; exact hS k' s hs
  | peek k f q ih => intro v S hS; exact ih hq _ S hS
  | pop k f q ih =>
    intro v S hS
    simp only [TM2.stepAux]
    apply ih hq
    intro k' s hs
    by_cases hk : k' = k
    · subst hk
      rw [Function.update_self] at hs
      exact hS k' s (List.mem_of_mem_tail hs)
    · rw [Function.update_of_ne hk] at hs; exact hS k' s hs
  | load a q ih => intro v S hS; exact ih hq _ S hS
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S hS
    simp only [TM2.stepAux]
    cases f v
    · exact ih₂ (fun x hx => hq (Or.inr hx)) v S hS
    · exact ih₁ (fun x hx => hq (Or.inl hx)) v S hS
  | goto f => intro v S hS; exact hS
  | halt => intro v S hS; exact hS

end stmt

section run

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

def stepT (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => TM2.stepAux (M l) c.var c.stk

theorem stepT_of_step (M : Λ → TM2.Stmt Γ Λ σ) (c c' : TM2.Cfg Γ Λ σ)
    (h : TM2.step M c = some c') : stepT M c = c' := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l => simpa [TM2.step, stepT] using h

theorem stepT_none (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) (h : c.l = none) :
    stepT M c = c := by
  simp [stepT, h]

theorem iterate_stepT (M : Λ → TM2.Stmt Γ Λ σ) :
    ∀ (s : ℕ) (a b : TM2.Cfg Γ Λ σ), (flip bind (TM2.step M))^[s] (some a) = some b →
      b.l = none → ∀ m, s ≤ m → (stepT M)^[m] a = b := by
  intro s
  induction s with
  | zero =>
    intro a b hab hb m _
    have : a = b := Option.some.inj hab
    subst this
    exact Function.iterate_fixed (stepT_none M a hb) m
  | succ s ih =>
    intro a b hab hb m hm
    rw [Function.iterate_succ_apply] at hab
    cases hfa : TM2.step M a with
    | none =>
      have e : flip bind (TM2.step M) (some a) = none := hfa
      rw [e, MachNS.iterate_none] at hab
      exact absurd hab (by simp)
    | some c =>
      have e : flip bind (TM2.step M) (some a) = some c := hfa
      rw [e] at hab
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Function.iterate_succ_apply, stepT_of_step M a c hfa]
      exact ih c b hab hb m' (by omega)

theorem iterate_stepT_mem (M : Λ → TM2.Stmt Γ Λ σ) :
    ∀ (j : ℕ) (a : TM2.Cfg Γ Λ σ), ∃ s ≤ j,
      (flip bind (TM2.step M))^[s] (some a) = some ((stepT M)^[j] a) := by
  intro j
  induction j with
  | zero => intro a; exact ⟨0, le_rfl, rfl⟩
  | succ j ih =>
    intro a
    cases hfa : TM2.step M a with
    | none =>
      have hl : a.l = none := by
        obtain ⟨l, v, S⟩ := a
        cases l with
        | none => rfl
        | some l => simp [TM2.step] at hfa
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [Function.iterate_fixed (stepT_none M a hl)]; rfl
    | some c =>
      obtain ⟨s, hs, h⟩ := ih c
      refine ⟨s + 1, by omega, ?_⟩
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepT_of_step M a c hfa]
      have e : flip bind (TM2.step M) (some a) = some c := hfa
      rw [e]; exact h

end run

end TabNS
end

section
open Turing

namespace TabNS

open EnumNS
open Classical

section enc

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

noncomputable def symBit {T : Set (Σ k, Γ k)} (k : K) (o : Option (Γ k)) (g : T) : Bool :=
  decide (o.map (Sigma.mk k) = some g.1)

theorem symBit_inj {T : Set (Σ k, Γ k)} (k : K) (o o' : Option (Γ k))
    (ho : ∀ s, o = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T)
    (ho' : ∀ s, o' = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T)
    (h : ∀ g : T, symBit k o g = symBit k o' g) : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some s' =>
      have := h ⟨⟨k, s'⟩, ho' s' rfl⟩
      simp [symBit] at this
  | some s =>
    have := h ⟨⟨k, s⟩, ho s rfl⟩
    simp only [symBit, Option.map_some, decide_true] at this
    cases o' with
    | none => simp at this
    | some s' =>
      simp only [Option.map_some, Option.some.injEq] at this
      have := (Sigma.mk.inj (decide_eq_true_iff.1 this.symm)).2
      rw [eq_of_heq this]

abbrev Idx (Λ σ : Type) (T : Set (Σ k, Γ k)) (H : ℕ) : Type :=
  Option Λ ⊕ σ ⊕ (K × Fin H × T) ⊕ (K × Fin H)

abbrev Wix (Λ σ : Type) (T : Set (Σ k, Γ k)) (d : ℕ) : Type :=
  Option Λ ⊕ σ ⊕ (K × Fin d × T)

variable (T : Set (Σ k, Γ k)) (H d : ℕ)

noncomputable def enc (c : TM2.Cfg Γ Λ σ) : Idx Λ σ T H → Bool
  | .inl l => decide (c.l = l)
  | .inr (.inl s) => decide (c.var = s)
  | .inr (.inr (.inl (k, i, g))) => symBit k ((c.stk k).reverse[i.1]?) g
  | .inr (.inr (.inr (k, i))) => decide (i.1 < (c.stk k).length)

noncomputable def wenc (c : TM2.Cfg Γ Λ σ) : Wix Λ σ T d → Bool
  | .inl l => decide (c.l = l)
  | .inr (.inl s) => decide (c.var = s)
  | .inr (.inr (k, r, g)) => symBit k ((c.stk k)[r.1]?) g

theorem good_getElem? {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) (l : List (Γ k))
    (hl : ∀ s ∈ l, s ∈ S k) (j : ℕ) : ∀ s, l[j]? = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T := by
  intro s hs
  exact hS k s (hl s (List.mem_of_getElem? hs))

theorem window_det (c c' : TM2.Cfg Γ Λ σ) (hc : Good T c.stk) (hc' : Good T c'.stk)
    (h : wenc T d c = wenc T d c') :
    c.l = c'.l ∧ c.var = c'.var ∧ ∀ k, (c.stk k).take d = (c'.stk k).take d := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun h (.inl c.l)
    simp only [wenc, decide_true] at this
    exact (decide_eq_true_iff.1 this.symm).symm
  · have := congrFun h (.inr (.inl c.var))
    simp only [wenc, decide_true] at this
    exact (decide_eq_true_iff.1 this.symm).symm
  · intro k
    apply List.ext_getElem?
    intro r
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hr
    · apply symBit_inj (T := T) k
      · exact good_getElem? T hc k _ (fun s hs => hs) r
      · exact good_getElem? T hc' k _ (fun s hs => hs) r
      · intro g
        exact congrFun h (.inr (.inr (k, ⟨r, hr⟩, g)))
    · rfl

variable (M : Λ → TM2.Stmt Γ Λ σ)

def newTop (l : Λ) (c : TM2.Cfg Γ Λ σ) (k : K) : List (Γ k) :=
  (TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).stk k

theorem stepT_some (hd : ∀ l, pops (M l) ≤ d) (c : TM2.Cfg Γ Λ σ) (l : Λ) (hl : c.l = some l) :
    stepT M c = ⟨(TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).l,
      (TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).var,
      fun k => newTop d M l c k ++ (c.stk k).drop d⟩ := by
  simp only [stepT, hl]
  exact stepAux_take (M l) d (hd l) c.var c.stk

theorem newTop_length (p : ℕ) (hp : ∀ l, MachNS.pushes (M l) ≤ p)
    (l : Λ) (c : TM2.Cfg Γ Λ σ) (k : K) :
    (newTop d M l c k).length ≤ min (c.stk k).length d + p := by
  have h1 := MachNS.stepAux_length (M l) c.var
    (fun k => (c.stk k).take d) k
  have h2 := hp l
  simp only [List.length_take] at h1
  unfold newTop
  omega

theorem stepT_det_l (hd : ∀ l, pops (M l) ≤ d) (c c' : TM2.Cfg Γ Λ σ) (hc : Good T c.stk)
    (hc' : Good T c'.stk) (h : wenc T d c = wenc T d c') :
    (stepT M c).l = (stepT M c').l ∧ (stepT M c).var = (stepT M c').var := by
  obtain ⟨h1, h2, h3⟩ := window_det T d c c' hc hc' h
  cases hl : c.l with
  | none =>
    have hl' : c'.l = none := by rw [← h1, hl]
    rw [stepT_none M c hl, stepT_none M c' hl']
    exact ⟨by rw [hl, hl'], h2⟩
  | some l =>
    have hl' : c'.l = some l := by rw [← h1, hl]
    rw [stepT_some d M hd c l hl, stepT_some d M hd c' l hl']
    have e : (fun k => (c.stk k).take d) = (fun k => (c'.stk k).take d) := funext h3
    simp only [e, h2]
    exact ⟨trivial, trivial⟩

def newCell {α : Type} (r : List α) (h : ℕ) (o : Option α) (i : ℕ) : Option α :=
  if i < h - d then o else r.reverse[i - (h - d)]?

theorem newCell_true {α : Type} (r S : List α) (i : ℕ) :
    (r ++ S.drop d).reverse[i]? = newCell d r S.length S.reverse[i]? i := by
  unfold newCell
  rw [List.reverse_append, List.getElem?_append, List.length_reverse, List.length_drop]
  split_ifs with h
  · have e : S.reverse = (S.drop d).reverse ++ (S.take d).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e, List.getElem?_append_left (by rw [List.length_reverse, List.length_drop]; exact h)]
  · rfl

variable (p : ℕ)

def rad : ℕ := d + p + 1

def clampH (h i : ℕ) : ℕ := min (2 * rad d p) (h + rad d p - i) + i - rad d p

theorem newCell_clamp {α : Type} (r : List α) (h : ℕ) (o : Option α) (i : ℕ)
    (hr : r.length ≤ d + p) : newCell d r h o i = newCell d r (clampH d p h i) o i := by
  unfold newCell clampH rad
  rcases Nat.lt_or_ge h (i + (d + p + 1)) with h1 | h1
  · rcases Nat.lt_or_ge i (h + (d + p + 1)) with h2 | h2
    · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) = h := by omega
      rw [e]
    · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) =
          i - (d + p + 1) := by omega
      rw [e, if_neg (show ¬ _ by omega), if_neg (show ¬ _ by omega), List.getElem?_eq_none, List.getElem?_eq_none]
      · rw [List.length_reverse]; omega
      · rw [List.length_reverse]; omega
  · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) =
        i + (d + p + 1) := by omega
    rw [e, if_pos (by omega), if_pos (by omega)]

theorem newMark_clamp (rl h i : ℕ) (hr : rl ≤ d + p) :
    i < rl + (h - d) ↔ i < rl + (clampH d p h i - d) := by
  unfold clampH rad; omega

theorem oldMark_clamp (h i : ℕ) : i < h ↔ rad d p < min (2 * rad d p) (h + rad d p - i) := by
  unfold rad; omega

noncomputable def locenc (c : TM2.Cfg Γ Λ σ) (k : K) (i : ℕ) :
    Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T → Bool
  | .inl w => wenc T d c w
  | .inr (.inl δ) => decide (δ.1 + i < (c.stk k).length + rad d p)
  | .inr (.inr g) => symBit k ((c.stk k).reverse[i]?) g

theorem cnt_det (R h h' i : ℕ)
    (H : ∀ δ : Fin (2 * R), decide (δ.1 + i < h + R) = decide (δ.1 + i < h' + R)) :
    min (2 * R) (h + R - i) = min (2 * R) (h' + R - i) := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hb : min (2 * R) (h + R - i) < 2 * R := by omega
    have := H ⟨_, hb⟩
    simp only [decide_eq_decide] at this
    omega
  · have hb : min (2 * R) (h' + R - i) < 2 * R := by omega
    have := H ⟨_, hb⟩
    simp only [decide_eq_decide] at this
    omega

theorem locenc_det (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, MachNS.pushes (M l) ≤ p) (c c' : TM2.Cfg Γ Λ σ) (k : K) (i : ℕ)
    (hc : Good T c.stk) (hc' : Good T c'.stk) (h : locenc T d p c k i = locenc T d p c' k i) :
    ((stepT M c).stk k).reverse[i]? = ((stepT M c').stk k).reverse[i]? ∧
      (i < ((stepT M c).stk k).length ↔ i < ((stepT M c').stk k).length) := by
  have hw : wenc T d c = wenc T d c' := funext fun w => congrFun h (.inl w)
  obtain ⟨h1, h2, h3⟩ := window_det T d c c' hc hc' hw
  have ho : (c.stk k).reverse[i]? = (c'.stk k).reverse[i]? := by
    apply symBit_inj (T := T) k
    · exact good_getElem? T hc k _ (fun s hs => List.mem_reverse.1 hs) i
    · exact good_getElem? T hc' k _ (fun s hs => List.mem_reverse.1 hs) i
    · intro g; exact congrFun h (.inr (.inr g))
  have hn := cnt_det (rad d p) (c.stk k).length (c'.stk k).length i
    (fun δ => congrFun h (.inr (.inl δ)))
  have hcl : clampH d p (c.stk k).length i = clampH d p (c'.stk k).length i := by
    unfold clampH; rw [hn]
  cases hl : c.l with
  | none =>
    have hl' : c'.l = none := by rw [← h1, hl]
    rw [stepT_none M c hl, stepT_none M c' hl']
    refine ⟨ho, ?_⟩
    rw [oldMark_clamp d p (c.stk k).length i, oldMark_clamp d p (c'.stk k).length i, hn]
  | some l =>
    have hl' : c'.l = some l := by rw [← h1, hl]
    rw [stepT_some d M hd c l hl, stepT_some d M hd c' l hl']
    have hr : newTop d M l c k = newTop d M l c' k := by
      unfold newTop
      have e : (fun k => (c.stk k).take d) = (fun k => (c'.stk k).take d) := funext h3
      rw [e, h2]
    have hlen := newTop_length d M p hp l c k
    have hlen' : (newTop d M l c k).length ≤ d + p := by omega
    simp only
    refine ⟨?_, ?_⟩
    · rw [newCell_true, newCell_true, newCell_clamp d p _ _ _ _ hlen', ho, hcl, hr,
        ← newCell_clamp d p _ _ _ _ (hr ▸ hlen')]
    · rw [List.length_append, List.length_append, List.length_drop, List.length_drop,
        newMark_clamp d p _ _ _ hlen', hcl, hr, ← newMark_clamp d p _ _ _ (hr ▸ hlen')]

end enc

end TabNS
end

section
open Turing

namespace TabNS

open EnumNS
open Classical

def orL {α : Type} : List (Ex α) → Ex α
  | [] => .const false
  | e :: l => .or e (orL l)

theorem eval_orL {α : Type} (ρ : α → Bool) (l : List (Ex α)) :
    Ex.eval ρ (orL l) = l.any (Ex.eval ρ) := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [orL, Ex.eval, ih]

theorem size_orL {α : Type} (l : List (Ex α)) :
    Ex.size (orL l) = (l.map Ex.size).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons e l ih => simp [orL, Ex.size, ih]; omega

section step

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} [Fintype Λ]
  [Fintype σ] (T : Set (Σ k, Γ k)) [Fintype T] (H d p : ℕ)

def Bounded (c : TM2.Cfg Γ Λ σ) : Prop := ∀ k, (c.stk k).length ≤ H

def Ubit (k : K) (m : ℕ) : Ex (Idx Λ σ T H) :=
  if h : m < H then .var (.inr (.inr (.inr (k, ⟨m, h⟩)))) else .const false

theorem eval_Ubit (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (k : K) (m : ℕ) :
    Ex.eval (enc T H c) (Ubit (Λ := Λ) (σ := σ) T H k m) = decide (m < (c.stk k).length) := by
  unfold Ubit
  split_ifs with h
  · rfl
  · have := hc k
    simp only [Ex.eval]
    symm; rw [decide_eq_false_iff_not]; omega

theorem size_Ubit (k : K) (m : ℕ) : Ex.size (Ubit (Λ := Λ) (σ := σ) T H k m) = 1 := by
  unfold Ubit; split_ifs <;> rfl

noncomputable def eA : Idx Λ σ T H ⊕ Wix Λ σ T d → Ex (Idx Λ σ T H)
  | .inl j => .var j
  | .inr (.inl l) => .var (.inl l)
  | .inr (.inr (.inl s)) => .var (.inr (.inl s))
  | .inr (.inr (.inr (k, r, g))) =>
    orL ((List.finRange H).map fun i =>
      .and (.and (Ubit T H k (i.1 + r.1)) (.not (Ubit T H k (i.1 + r.1 + 1))))
        (.var (.inr (.inr (.inl (k, i, g))))))

theorem size_eA (b : Idx Λ σ T H ⊕ Wix Λ σ T d) : Ex.size (eA T H d b) ≤ 7 * H + 1 := by
  rcases b with j | l | s | ⟨k, r, g⟩
  · simp [eA, Ex.size]
  · simp [eA, Ex.size]
  · simp [eA, Ex.size]
  · simp only [eA, size_orL, List.length_map, List.length_finRange, List.map_map]
    have : ∀ x ∈ List.map (Ex.size ∘ fun i : Fin H =>
        Ex.and (Ex.and (Ubit (Λ := Λ) (σ := σ) T H k (i.1 + r.1))
          (Ex.not (Ubit T H k (i.1 + r.1 + 1))))
          (Ex.var (Sum.inr (Sum.inr (Sum.inl (k, i, g)))))) (List.finRange H), x = 6 := by
      intro x hx
      simp only [List.mem_map, Function.comp] at hx
      obtain ⟨i, _, rfl⟩ := hx
      simp [Ex.size, size_Ubit]
    rw [List.sum_eq_card_nsmul _ 6 this]
    simp; omega

theorem eval_eA (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (b : Idx Λ σ T H ⊕ Wix Λ σ T d) :
    Ex.eval (enc T H c) (eA T H d b) = Sum.elim (enc T H c) (wenc T d c) b := by
  rcases b with j | l | s | ⟨k, r, g⟩
  · rfl
  · rfl
  · rfl
  · simp only [eA, eval_orL, Sum.elim_inr, wenc]
    rw [Bool.eq_iff_iff, List.any_map, List.any_eq_true]
    simp only [List.mem_finRange, true_and, Function.comp, Ex.eval, eval_Ubit T H c hc,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not, enc]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, h3⟩
      have hi : i.1 < (c.stk k).length := by omega
      rw [List.getElem?_reverse hi] at h3
      have e : (c.stk k).length - 1 - i.1 = r.1 := by omega
      rw [e] at h3; exact h3
    · intro h
      have hr : r.1 < (c.stk k).length := by
        by_contra hr
        rw [List.getElem?_eq_none (by omega)] at h
        simp [symBit] at h
      have hH := hc k
      refine ⟨⟨(c.stk k).length - 1 - r.1, by omega⟩, ⟨by simp; omega, by simp; omega⟩, ?_⟩
      rw [List.getElem?_reverse (by simp; omega)]
      have e : (c.stk k).length - 1 - ((c.stk k).length - 1 - r.1) = r.1 := by omega
      simp only [e]; exact h

noncomputable def tau (k : K) (i : Fin H) :
    Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T → Ex (Idx Λ σ T H ⊕ Wix Λ σ T d)
  | .inl w => .var (.inr w)
  | .inr (.inl δ) =>
    if δ.1 + i.1 < rad d p then .const true
    else if h : δ.1 + i.1 - rad d p < H then .var (.inl (.inr (.inr (.inr (k, ⟨_, h⟩)))))
    else .const false
  | .inr (.inr g) => .var (.inl (.inr (.inr (.inl (k, i, g)))))

theorem size_tau (k : K) (i : Fin H) (v : Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) :
    Ex.size (tau T H d p k i v) = 1 := by
  rcases v with w | δ | g
  · rfl
  · simp only [tau]; split_ifs <;> rfl
  · rfl

theorem eval_tau (c : TM2.Cfg Γ Λ σ) (hc : Bounded H c) (k : K) (i : Fin H)
    (v : Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) :
    Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v) = locenc T d p c k i.1 v := by
  rcases v with w | δ | g
  · rfl
  · simp only [tau, locenc]
    have hH := hc k
    split_ifs with h1 h2
    · simp only [Ex.eval]; symm; rw [decide_eq_true_iff]; omega
    · simp only [Ex.eval, Sum.elim_inl, enc, decide_eq_decide]; omega
    · simp only [Ex.eval]; symm; rw [decide_eq_false_iff_not]; omega
  · rfl

noncomputable def CB : ℕ :=
  7 * 2 ^ (Fintype.card (Wix Λ σ T d) + 2 * rad d p + Fintype.card T)

theorem exists_eB (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, MachNS.pushes (M l) ≤ p) :
    ∃ eB : Idx Λ σ T H → Ex (Idx Λ σ T H ⊕ Wix Λ σ T d),
      (∀ j, Ex.size (eB j) ≤ CB (Λ := Λ) (σ := σ) T d p) ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c → ∀ j,
        Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (eB j) = enc T H (stepT M c) j := by
  have hW : 7 * 2 ^ Fintype.card (Wix Λ σ T d) ≤ CB (Λ := Λ) (σ := σ) T d p := by
    unfold CB
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hL : 7 * 2 ^ Fintype.card (Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T) ≤
      CB (Λ := Λ) (σ := σ) T d p := by
    unfold CB
    simp [Fintype.card_sum, Nat.add_assoc]
  have key : ∀ j : Idx Λ σ T H, ∃ E : Ex (Idx Λ σ T H ⊕ Wix Λ σ T d),
      Ex.size E ≤ CB (Λ := Λ) (σ := σ) T d p ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c →
        Ex.eval (Sum.elim (enc T H c) (wenc T d c)) E = enc T H (stepT M c) j := by
    intro j
    rcases j with l' | s' | ⟨k, i, g⟩ | ⟨k, i⟩
    · obtain ⟨E, hs, he⟩ := exists_ex_det (wenc T d) (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide ((stepT M c).l = l'))
        (fun x y hx hy h => by rw [(stepT_det_l T d M hd x y hx hy h).1])
      refine ⟨Ex.bind (fun w => .var (.inr w)) E, ?_, fun c hc _ => ?_⟩
      · rw [Ex.size_bind _ (fun _ => rfl)]; omega
      · rw [Ex.eval_bind]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (wenc T d) (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide ((stepT M c).var = s'))
        (fun x y hx hy h => by rw [(stepT_det_l T d M hd x y hx hy h).2])
      refine ⟨Ex.bind (fun w => .var (.inr w)) E, ?_, fun c hc _ => ?_⟩
      · rw [Ex.size_bind _ (fun _ => rfl)]; omega
      · rw [Ex.eval_bind]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (fun c => locenc T d p c k i.1)
        (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => symBit k (((stepT M c).stk k).reverse[i.1]?) g)
        (fun x y hx hy h => by rw [(locenc_det T d M p hd hp x y k i.1 hx hy h).1])
      refine ⟨Ex.bind (tau T H d p k i) E, ?_, fun c hc hb => ?_⟩
      · rw [Ex.size_bind _ (size_tau T H d p k i)]; omega
      · rw [Ex.eval_bind]
        have e : (fun v => Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v)) =
            locenc T d p c k i.1 := funext (eval_tau T H d p c hb k i)
        rw [e]; exact he c hc
    · obtain ⟨E, hs, he⟩ := exists_ex_det (fun c => locenc T d p c k i.1)
        (fun c : TM2.Cfg Γ Λ σ => Good T c.stk)
        (fun c => decide (i.1 < ((stepT M c).stk k).length))
        (fun x y hx hy h => by
          simp only [decide_eq_decide]; exact (locenc_det T d M p hd hp x y k i.1 hx hy h).2)
      refine ⟨Ex.bind (tau T H d p k i) E, ?_, fun c hc hb => ?_⟩
      · rw [Ex.size_bind _ (size_tau T H d p k i)]; omega
      · rw [Ex.eval_bind]
        have e : (fun v => Ex.eval (Sum.elim (enc T H c) (wenc T d c)) (tau T H d p k i v)) =
            locenc T d p c k i.1 := funext (eval_tau T H d p c hb k i)
        rw [e]; exact he c hc
  choose eB h1 h2 using key
  exact ⟨eB, h1, fun c hc hb j => h2 j c hc hb⟩

theorem sim_step (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, MachNS.pushes (M l) ≤ p) :
    ∃ F : (Idx Λ σ T H → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H ⊕ Wix (K := K) Λ σ T d) * (7 * H + 1) +
        Fintype.card (Idx (K := K) Λ σ T H) * CB (Λ := Λ) (σ := σ) T d p) ∧
      ∀ c : TM2.Cfg Γ Λ σ, Good T c.stk → Bounded H c → F (enc T H c) = enc T H (stepT M c) := by
  obtain ⟨eB, hs, he⟩ := exists_eB T H d p M hd hp
  have hA := sim_layer (eA (Λ := Λ) (σ := σ) T H d)
  have hB := sim_layer eB
  refine ⟨_, sim_mono (sim_comp hA hB) ?_, fun c hc hb => ?_⟩
  · apply add_le_add
    · refine (Finset.sum_le_card_nsmul _ _ _ (fun b _ => size_eA T H d b)).trans ?_
      simp
    · refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => hs j)).trans ?_
      simp
  · funext j
    have e : (fun b => Ex.eval (enc T H c) (eA T H d b)) = Sum.elim (enc T H c) (wenc T d c) :=
      funext (eval_eA T H d c hb)
    simp only [e]
    exact he c hc hb j

end step

end TabNS
end

section
open Turing

namespace TabNS

open EnumNS
open Classical

section run

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} [Fintype Λ]
  [Fintype σ] (T : Set (Σ k, Γ k)) [Fintype T] (H d p : ℕ)
  (k₀ : K) (main : Λ) (s0 : σ) (ι : Bool → Γ k₀)

def initCfg {n : ℕ} (ρ : Fin n → Bool) : TM2.Cfg Γ Λ σ :=
  ⟨some main, s0, Function.update (fun _ => []) k₀ ((List.ofFn ρ).map ι)⟩

theorem init_det {n : ℕ} (ρ ρ' : Fin n → Bool) (k : K) (i : ℕ)
    (h : ∀ hi : i < n, ρ ⟨n - 1 - i, by omega⟩ = ρ' ⟨n - 1 - i, by omega⟩) :
    ((initCfg k₀ main s0 ι ρ).stk k).reverse[i]? =
      ((initCfg k₀ main s0 ι ρ').stk k).reverse[i]? := by
  by_cases hk : k = k₀
  · subst hk
    simp only [initCfg, Function.update_self]
    by_cases hi : i < n
    · rw [List.getElem?_reverse (by simpa using hi), List.getElem?_reverse (by simpa using hi)]
      simp only [List.length_map, List.length_ofFn, List.getElem?_map, List.getElem?_ofFn]
      rw [dif_pos (by omega), dif_pos (by omega)]
      simp only [Option.map_some]
      rw [h hi]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · simp [initCfg, Function.update_of_ne hk]

theorem init_len {n : ℕ} (ρ : Fin n → Bool) (k : K) :
    ((initCfg k₀ main s0 ι ρ).stk k).length = if k = k₀ then n else 0 := by
  by_cases hk : k = k₀
  · subst hk; simp [initCfg]
  · simp [initCfg, hk]

theorem sim_init (n : ℕ) :
    ∃ F : (Fin n → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H) * 14) ∧
      ∀ ρ, F ρ = enc T H (initCfg k₀ main s0 ι ρ) := by
  have key : ∀ j : Idx Λ σ T H, ∃ E : Ex (Fin n), Ex.size E ≤ 14 ∧
      ∀ ρ, Ex.eval ρ E = enc T H (initCfg k₀ main s0 ι ρ) j := by
    intro j
    rcases j with l | s | ⟨k, i, g⟩ | ⟨k, i⟩
    · exact ⟨.const (decide (some main = l)), by simp [Ex.size], fun ρ => rfl⟩
    · exact ⟨.const (decide (s0 = s)), by simp [Ex.size], fun ρ => rfl⟩
    · let v : Unit → Ex (Fin n) := fun _ =>
        if hi : i.1 < n then .var ⟨n - 1 - i.1, by omega⟩ else .const false
      have hv : ∀ u, Ex.size (v u) = 1 := by intro u; simp only [v]; split_ifs <;> rfl
      obtain ⟨E, hs, he⟩ := exists_ex_det (V := Unit)
        (fun ρ (_ : Unit) => Ex.eval ρ (v ())) (fun _ => True)
        (fun ρ => enc T H (initCfg k₀ main s0 ι ρ) (.inr (.inr (.inl (k, i, g)))))
        (fun x y _ _ hxy => by
          simp only [enc]
          rw [init_det k₀ main s0 ι x y k i.1]
          intro hi
          have := congrFun hxy ()
          simpa [v, hi, Ex.eval] using this)
      refine ⟨Ex.bind v E, ?_, fun ρ => ?_⟩
      · rw [Ex.size_bind v hv]; simp at hs; omega
      · rw [Ex.eval_bind]; exact he ρ trivial
    · refine ⟨.const (decide (i.1 < if k = k₀ then n else 0)), by simp [Ex.size], fun ρ => ?_⟩
      simp only [Ex.eval, enc, init_len]
  choose eI h1 h2 using key
  refine ⟨_, sim_mono (sim_layer eI) ?_, fun ρ => funext fun j => h2 j ρ⟩
  refine (Finset.sum_le_card_nsmul _ _ _ (fun j _ => h1 j)).trans ?_
  simp

theorem stepT_len (M : Λ → TM2.Stmt Γ Λ σ)
    (hp : ∀ l, MachNS.pushes (M l) ≤ p) (c : TM2.Cfg Γ Λ σ) (k : K) :
    ((stepT M c).stk k).length ≤ (c.stk k).length + p := by
  cases hl : c.l with
  | none => rw [stepT_none M c hl]; omega
  | some l =>
    simp only [stepT, hl]
    exact (MachNS.stepAux_length _ _ _ _).trans (by have := hp l; omega)

theorem stepT_good (M : Λ → TM2.Stmt Γ Λ σ) (hT : ∀ l, pushSet (M l) ⊆ T) (c : TM2.Cfg Γ Λ σ)
    (hc : Good T c.stk) : Good T (stepT M c).stk := by
  cases hl : c.l with
  | none => rw [stepT_none M c hl]; exact hc
  | some l =>
    simp only [stepT, hl]
    exact good_stepAux T (M l) (hT l) c.var c.stk hc

theorem run_bits (M : Λ → TM2.Stmt Γ Λ σ) (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, MachNS.pushes (M l) ≤ p) (hT : ∀ l, pushSet (M l) ⊆ T)
    (hι : ∀ b, (⟨k₀, ι b⟩ : Σ k, Γ k) ∈ T) (n tt : ℕ) (hH : n + p * tt ≤ H) :
    ∃ F : (Fin n → Bool) → (Idx Λ σ T H → Bool),
      Sim F (Fintype.card (Idx (K := K) Λ σ T H) * 14 +
        tt * (Fintype.card (Idx (K := K) Λ σ T H ⊕ Wix (K := K) Λ σ T d) * (7 * H + 1) +
          Fintype.card (Idx (K := K) Λ σ T H) * CB (Λ := Λ) (σ := σ) T d p)) ∧
      ∀ ρ, F ρ = enc T H ((stepT M)^[tt] (initCfg k₀ main s0 ι ρ)) := by
  obtain ⟨FI, hI, eI⟩ := sim_init T H k₀ main s0 ι n
  obtain ⟨FSx, hS, eS⟩ := sim_step T H d p M hd hp
  refine ⟨fun ρ => FSx^[tt] (FI ρ), sim_comp hI (sim_iter hS tt), fun ρ => ?_⟩

  have hgood : ∀ j, Good T ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)).stk := by
    intro j
    induction j with
    | zero =>
      intro k s hs
      by_cases hk : k = k₀
      · subst hk
        simp only [Function.iterate_zero, id, initCfg, Function.update_self, List.mem_map] at hs
        obtain ⟨b, _, rfl⟩ := hs
        exact hι b
      · simp [initCfg, Function.update_of_ne hk] at hs
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact stepT_good T M hT _ ih
  have hlen : ∀ j k, (((stepT M)^[j] (initCfg k₀ main s0 ι ρ)).stk k).length ≤ n + p * j := by
    intro j
    induction j with
    | zero =>
      intro k
      simp only [Function.iterate_zero, id, init_len]
      split_ifs <;> omega
    | succ j ih =>
      intro k
      rw [Function.iterate_succ_apply']
      have := stepT_len p M hp ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)) k
      have := ih k
      rw [Nat.mul_succ]; omega
  have main' : ∀ j, j ≤ tt →
      FSx^[j] (FI ρ) = enc T H ((stepT M)^[j] (initCfg k₀ main s0 ι ρ)) := by
    intro j
    induction j with
    | zero => intro _; simp [eI]
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      apply eS _ (hgood j)
      intro k
      have := hlen j k
      have : p * j ≤ p * tt := Nat.mul_le_mul_left _ (by omega)
      omega
  exact main' tt le_rfl

end run

end TabNS
end

section
open Turing

namespace TabNS

open EnumNS
open PEqualNP.CircuitLowerBounds
open Classical

theorem arith (A W0 CB P X Y tt : ℕ) (hY : Y ≤ P * X) (ht : tt ≤ X) (hX : 1 ≤ X) :
    14 * A * Y + tt * ((A * Y + W0) * (7 * Y) + A * Y * CB) ≤
      (14 * A * P + (A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by
  have hX2 : X ≤ X ^ 3 := by nlinarith [pow_le_pow_right₀ hX (show 1 ≤ 3 by norm_num), pow_one X]
  have h1 : 14 * A * Y + tt * ((A * Y + W0) * (7 * Y) + A * Y * CB) ≤
      14 * A * (P * X) + X * ((A * (P * X) + W0 * X) * (7 * (P * X)) + A * (P * X) * (CB * X)) := by
    have : W0 ≤ W0 * X := Nat.le_mul_of_pos_right _ hX
    have : CB ≤ CB * X := Nat.le_mul_of_pos_right _ hX
    gcongr
  refine h1.trans ?_
  have e : 14 * A * (P * X) + X * ((A * (P * X) + W0 * X) * (7 * (P * X)) + A * (P * X) * (CB * X))
      = 14 * A * P * X + ((A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by ring
  rw [e]
  have e2 : (14 * A * P + (A * P + W0) * 7 * P + A * P * CB) * X ^ 3 =
      14 * A * P * X ^ 3 + ((A * P + W0) * 7 * P + A * P * CB) * X ^ 3 := by ring
  rw [e2]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hX2) _

theorem dtime_size (t : ℕ → ℕ) (L : Language Bool) (hL : L ∈ PEqualNP.Library.DTIME t) :
    ∃ c : ℕ, L ∈ SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3) := by
  obtain ⟨f, hf, cm, hcm⟩ := hL
  let tm := cm.tm
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  let ι : Bool → tm.Γ tm.k₀ := cm.inputAlphabet.invFun
  let ι' : Bool → tm.Γ tm.k₁ := cm.outputAlphabet.invFun
  let T : Set (Σ k, tm.Γ k) := ((⋃ l, pushSet (tm.m l)) ∪
    Set.range (fun b => (⟨tm.k₀, ι b⟩ : Σ k, tm.Γ k))) ∪ {⟨tm.k₁, ι' true⟩}
  have hTfin : T.Finite :=
    ((Set.finite_iUnion fun l => pushSet_finite (tm.m l)).union (Set.finite_range _)).union
      (Set.finite_singleton _)
  letI : Fintype T := hTfin.fintype
  have hT : ∀ l, pushSet (tm.m l) ⊆ T := fun l x hx =>
    Or.inl (Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩))
  have hι : ∀ b, (⟨tm.k₀, ι b⟩ : Σ k, tm.Γ k) ∈ T := fun b => Or.inl (Or.inr ⟨b, rfl⟩)
  have hgT : (⟨tm.k₁, ι' true⟩ : Σ k, tm.Γ k) ∈ T := Or.inr rfl
  let d : ℕ := Finset.univ.sup fun l => pops (tm.m l)
  let p : ℕ := MachNS.maxPush tm
  have hd : ∀ l, pops (tm.m l) ≤ d := fun l =>
    Finset.le_sup (f := fun l => pops (tm.m l)) (Finset.mem_univ l)
  have hp : ∀ l, MachNS.pushes (tm.m l) ≤ p := fun l =>
    Finset.le_sup (f := fun l => MachNS.pushes (tm.m l)) (Finset.mem_univ l)
  let A : ℕ := Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
    Fintype.card tm.K * Fintype.card T + Fintype.card tm.K
  let W0 : ℕ := Fintype.card (Wix (K := tm.K) tm.Λ tm.σ T d)
  let C0 : ℕ := CB (Λ := tm.Λ) (σ := tm.σ) T d p
  let P : ℕ := p + 2
  refine ⟨14 * A * P + (A * P + W0) * 7 * P + A * P * C0, fun n => ?_⟩
  let H : ℕ := n + p * t n + 1
  obtain ⟨F, hF, eF⟩ := run_bits T H d p tm.k₀ tm.main tm.initialState ι tm.m hd hp hT hι n
    (t n) (by omega)
  obtain ⟨gs, w', hbasic, hlen, hsem⟩ := hF n (fun i : Fin n => i.1)
  let gT : T := ⟨⟨tm.k₁, ι' true⟩, hgT⟩
  let oIdx : Idx (K := tm.K) tm.Λ tm.σ T H := .inr (.inr (.inl (tm.k₁, ⟨0, by omega⟩, gT)))
  refine ⟨⟨gs, w' oIdx⟩, hbasic, ?_, ?_⟩
  ·
    change gs.length ≤ _
    refine hlen.trans ?_
    have hcI : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) ≤ A * (H + 1) := by
      simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, A]
      nlinarith
    have hcIW : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H ⊕ Wix (K := tm.K) tm.Λ tm.σ T d) ≤
        A * (H + 1) + W0 := by
      rw [Fintype.card_sum]; omega
    have h7 : 7 * H + 1 ≤ 7 * (H + 1) := by omega
    have step1 : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * 14 +
        t n * (Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H ⊕ Wix (K := tm.K) tm.Λ tm.σ T d) *
          (7 * H + 1) + Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * C0) ≤
        14 * A * (H + 1) + t n * ((A * (H + 1) + W0) * (7 * (H + 1)) + A * (H + 1) * C0) := by
      have : Fintype.card (Idx (K := tm.K) tm.Λ tm.σ T H) * 14 ≤ 14 * A * (H + 1) := by
        nlinarith
      gcongr
    refine step1.trans (arith A W0 C0 P (t n + n + 1) (H + 1) (t n) ?_ (by omega) (by omega))
    simp only [H, P]
    nlinarith
  ·
    intro x hx
    subst hx
    let ρ : Fin x.length → Bool := fun i => x[i.1]
    have hrep : Rep x (fun i : Fin x.length => i.1) ρ := by
      intro i
      refine ⟨i.2, ?_⟩
      simp [ρ, List.getD_eq_getElem?_getD]
    have hout := (hsem x ρ rfl hrep oIdx).2
    rw [eF] at hout

    have hrun := cm.outputsFun x
    obtain ⟨⟨s, hs⟩, hsm⟩ := hrun
    have hinit : initList tm (List.map cm.inputAlphabet.invFun x) =
        initCfg tm.k₀ tm.main tm.initialState ι ρ := by
      rw [MachNS.initList_eq]
      simp only [initCfg, ρ, List.ofFn_getElem]
      rfl
    have hfinal : (stepT tm.m)^[t x.length] (initCfg tm.k₀ tm.main tm.initialState ι ρ) =
        haltList tm [ι' (f x)] := by
      rw [← hinit]
      exact iterate_stepT tm.m s _ _ hs rfl _ (hsm.trans (hcm _))
    rw [hfinal] at hout
    change Circuit.eval _ x = true ↔ x ∈ L
    unfold Circuit.eval
    rw [run_wires]
    change (run gs x).getD (w' oIdx) false = true ↔ x ∈ L
    rw [hout]
    refine Iff.trans ?_ (hf x).symm
    simp only [oIdx, enc, MachNS.haltList_eq, Function.update_self,
      List.reverse_singleton, symBit, gT, decide_eq_true_eq]
    simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and]
    constructor
    · intro h; exact cm.outputAlphabet.symm.injective h
    · intro h; rw [h]

end TabNS
end

section
theorem libL003 : ∀ L : Language Bool, L ∈ PEqualNP.Library.P ↔
    ∃ p : Polynomial ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => Polynomial.eval n p) := by
  intro L
  constructor
  · rintro ⟨f, hf, ⟨c⟩⟩
    exact ⟨c.time, f, hf, c.toTM2ComputableInTime, fun n => le_rfl⟩
  · rintro ⟨p, f, hf, c, hc⟩
    refine ⟨f, hf, ⟨⟨c.toTM2ComputableAux, p, fun a => ?_⟩⟩⟩
    exact ⟨(c.outputsFun a).toEvalsTo, (c.outputsFun a).steps_le_m.trans (hc _)⟩
end

section
theorem libL073 :
    ∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ,
      L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3) :=
  fun t L hL => TabNS.dtime_size t L hL
end

section
theorem libL006 :
    PEqualNP.Library.P ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro L hL
  obtain ⟨p, hp⟩ := (libL003 L).mp hL
  obtain ⟨c, hc⟩ := libL073 _ L hp
  refine ⟨Polynomial.C c * (p + Polynomial.X + 1) ^ 3, ?_⟩
  have e : (fun n : ℕ => Polynomial.eval n (Polynomial.C c * (p + Polynomial.X + 1) ^ 3)) =
      fun n : ℕ => c * (Polynomial.eval n p + n + 1) ^ 3 := by
    funext n
    simp
  rw [e]
  exact hc
end


open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def pw (n i : ℕ) : ℕ := if i < n then i else 2 * n + 2 * (i - n)

def nw (n i : ℕ) : ℕ := if i < n then n + i else 2 * n + 2 * (i - n) + 1

def posG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.and, g.inputs.map (pw n)⟩ else ⟨GateOp.or, []⟩
  | GateOp.or => ⟨GateOp.or, (g.inputs.filter (fun i => decide (i < L))).map (pw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.and, []⟩
    | a :: _ => if a < L then ⟨GateOp.and, [nw n a]⟩ else ⟨GateOp.and, []⟩

def negG (n L : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => if g.inputs.all (fun i => decide (i < L)) = true then ⟨GateOp.or, g.inputs.map (nw n)⟩ else ⟨GateOp.and, []⟩
  | GateOp.or => ⟨GateOp.and, (g.inputs.filter (fun i => decide (i < L))).map (nw n)⟩
  | _ => match g.inputs with
    | [] => ⟨GateOp.or, []⟩
    | a :: _ => if a < L then ⟨GateOp.or, [pw n a]⟩ else ⟨GateOp.or, []⟩

def Rel (n : ℕ) (U U' : List Bool) : Prop :=
  ∀ i, i < U.length → U'.getD (pw n i) false = U.getD i false ∧ U'.getD (nw n i) false = !U.getD i false

theorem dm1 : ∀ l : List Bool, (l.map fun b => !b).any id = !(l.all id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_and]

theorem dm2 : ∀ l : List Bool, (l.map fun b => !b).all id = !(l.any id) := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.any_cons, List.all_cons, ih, id, Bool.not_or]

theorem any_filter (p : ℕ → Bool) (f : ℕ → Bool) : ∀ ins : List ℕ, (∀ i ∈ ins, p i = false → f i = false) →
    ((ins.filter p).map f).any id = (ins.map f).any id := by
  intro ins
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    have iht := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    by_cases hp : p a = true
    · simp only [List.filter_cons, hp, if_true, List.map_cons, List.any_cons, iht]
    · have hp' : p a = false := by simpa using hp
      have hf := h a (List.mem_cons_self ..) hp'
      simp only [List.filter_cons, hp', Bool.false_eq_true, if_false, List.map_cons, List.any_cons, iht, hf, id,
        Bool.false_or]

theorem gate_dual (n L : ℕ) (U U' : List Bool) (hL : U.length = L) (hR : Rel n U U') (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (posG n L g).op.eval ((posG n L g).inputs.map fun i => U'.getD i false)
      = g.op.eval (g.inputs.map fun i => U.getD i false) ∧
    (negG n L g).op.eval ((negG n L g).inputs.map fun i => U'.getD i false)
      = !(g.op.eval (g.inputs.map fun i => U.getD i false)) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  have hinv : ∀ i, ¬ i < L → U.getD i false = false := fun i hi =>
    List.getD_eq_default _ _ (by omega)
  have hmp : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (pw n)).map (fun i => U'.getD i false) = l.map fun i => U.getD i false := by
    intro l hl
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).1
  have hmn : ∀ l : List ℕ, (∀ i ∈ l, i < L) → (l.map (nw n)).map (fun i => U'.getD i false)
      = (l.map fun i => U.getD i false).map fun b => !b := by
    intro l hl
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (hR i (by rw [hL]; exact hl i hi)).2
  rcases hop with rfl | rfl | rfl
  · by_cases hall : ins.all (fun i => decide (i < L)) = true
    · have hl : ∀ i ∈ ins, i < L := fun i hi => by simpa using List.all_eq_true.1 hall i hi
      simp only [posG, negG, hall, if_true]
      constructor
      · show ((ins.map (pw n)).map fun i => U'.getD i false).all id = (ins.map fun i => U.getD i false).all id
        rw [hmp ins hl]
      · show ((ins.map (nw n)).map fun i => U'.getD i false).any id = !((ins.map fun i => U.getD i false).all id)
        rw [hmn ins hl, dm1]
    · simp only [posG, negG, hall, if_false]
      have hf : (ins.map fun i => U.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hc
        apply hall
        rw [List.all_eq_true] at hc ⊢
        intro i hi
        by_contra hlt
        have h1 := hc (U.getD i false) (List.mem_map.2 ⟨i, hi, rfl⟩)
        rw [hinv i (by simpa using hlt)] at h1
        exact absurd h1 (by simp)
      constructor
      · show ([] : List Bool).any id = (ins.map fun i => U.getD i false).all id
        rw [hf]; rfl
      · show ([] : List Bool).all id = !((ins.map fun i => U.getD i false).all id)
        rw [hf]; rfl
  · have hl : ∀ i ∈ ins.filter (fun i => decide (i < L)), i < L := fun i hi => by
      simpa using (List.mem_filter.1 hi).2
    have hfa := any_filter (fun i => decide (i < L)) (fun i => U.getD i false) ins
      (fun i _ hp => hinv i (by simpa using hp))
    simp only [posG, negG]
    constructor
    · show (((ins.filter fun i => decide (i < L)).map (pw n)).map fun i => U'.getD i false).any id
        = (ins.map fun i => U.getD i false).any id
      rw [hmp _ hl, hfa]
    · show (((ins.filter fun i => decide (i < L)).map (nw n)).map fun i => U'.getD i false).all id
        = !((ins.map fun i => U.getD i false).any id)
      rw [hmn _ hl, dm2, hfa]
  · cases ins with
    | nil =>
      simp only [posG, negG]
      exact ⟨rfl, rfl⟩
    | cons a t =>
      by_cases ha : a < L
      · simp only [posG, negG, ha, if_true]
        have h1 := hR a (by rw [hL]; exact ha)
        constructor
        · show (U'.getD (nw n a) false && true) = !(U.getD a false)
          rw [h1.2, Bool.and_true]
        · show (U'.getD (pw n a) false || false) = !!(U.getD a false)
          rw [h1.1, Bool.or_false, Bool.not_not]
      · simp only [posG, negG, ha, if_false]
        have h0 := hinv a ha
        constructor
        · show true = !(U.getD a false)
          rw [h0]; rfl
        · show false = !!(U.getD a false)
          rw [h0]; rfl

def dual (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | L, g :: t => posG n L g :: negG n L g :: dual n (L + 1) t

theorem dual_len (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (dual n L gs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro L; rfl
  | cons g t ih => intro L; simp only [dual, List.length_cons, ih]; omega

theorem pn_ok (n L : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ((posG n L g).op = GateOp.and ∨ (posG n L g).op = GateOp.or) ∧ (posG n L g).inputs.length ≤ 2 ∧
    ((negG n L g).op = GateOp.and ∨ (negG n L g).op = GateOp.or) ∧ (negG n L g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  simp only at hlen
  have hfl := List.length_filter_le (fun i => decide (i < L)) ins
  cases op with
  | and => simp only [posG, negG]; split_ifs <;> simp <;> omega
  | or => simp only [posG, negG]; simp; omega
  | not =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | mod m =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp
  | maj =>
    cases ins with
    | nil => simp [posG, negG]
    | cons a t => simp only [posG, negG]; split_ifs <;> simp

theorem dual_ok (n : ℕ) : ∀ (gs : List Gate) (L : ℕ), (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∀ g ∈ dual n L gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro gs
  induction gs with
  | nil => intro L _ g hg; simp [dual] at hg
  | cons g0 t ih =>
    intro L h g hg
    simp only [dual, List.mem_cons] at hg
    have hp := pn_ok n L g0 (h g0 (List.mem_cons_self ..))
    rcases hg with rfl | rfl | hg
    · exact ⟨hp.1, hp.2.1⟩
    · exact ⟨hp.2.2.1, hp.2.2.2⟩
    · exact ih (L + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) g hg

theorem dual_sim (n : ℕ) : ∀ (gs : List Gate) (L : ℕ) (U U' : List Bool), U.length = L → n ≤ L →
    U'.length = 2 * n + 2 * (L - n) → Rel n U U' →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    Rel n (wf gs U) (wf (dual n L gs) U') := by
  intro gs
  induction gs with
  | nil => intro L U U' _ _ _ hR _; exact hR
  | cons g t ih =>
    intro L U U' hL hn hL' hR hop
    have hpl : ∀ i, i < L → pw n i < U'.length ∧ nw n i < U'.length := by
      intro i hi
      unfold pw nw
      constructor <;> split_ifs <;> omega
    have hg := gate_dual n L U U' hL hR g (hop g (List.mem_cons_self ..))
    generalize hv : g.op.eval (g.inputs.map fun i => U.getD i false) = v at hg
    have hR1 : Rel n U (U' ++ [v]) := by
      intro i hi
      have := hpl i (by omega)
      rw [getD_snoc_lt U' _ _ this.1, getD_snoc_lt U' _ _ this.2]
      exact hR i hi
    have hg2 := gate_dual n L U _ hL hR1 g (hop g (List.mem_cons_self ..))
    rw [hv] at hg2
    show Rel n (wf (g :: t) U) (wf (posG n L g :: negG n L g :: dual n (L + 1) t) U')
    rw [wf_cons, wf_cons, wf_cons, hv, hg.1, hg2.2]
    refine ih (L + 1) _ _ (by simp [hL]) (by omega) (by simp [hL']; omega) ?_
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i hi
    have hi' : i < L + 1 := by simpa [hL] using hi
    by_cases hil : i < L
    · have h12 := hpl i hil
      constructor
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.1,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).1
      · rw [getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; omega), getD_snoc_lt U' _ _ h12.2,
          getD_snoc_lt U _ _ (by omega)]
        exact (hR i (by omega)).2
    · have hie : i = L := by omega
      subst hie
      have e1 : pw n i = U'.length := by unfold pw; rw [if_neg (by omega)]; omega
      have e2 : nw n i = (U' ++ [v]).length := by
        unfold nw; rw [if_neg (by omega), List.length_append]; simp; omega
      constructor
      · rw [e1, getD_snoc_lt (U' ++ [v]) _ _ (by rw [List.length_append]; simp), getD_snoc_eq, ← hL, getD_snoc_eq]
      · rw [e2, getD_snoc_eq, ← hL, getD_snoc_eq]


theorem conv9020 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.Represents.HasLitSize n f (2 * s) := by
  intro n s f ⟨C, hF, hs, hf⟩
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := fun g hg => by
    simpa using (hF g hg).1
  refine ⟨⟨dual n n C.gates, if C.output < n + C.gates.length then pw n C.output else 2 * n + 2 * C.gates.length⟩,
    fun g hg => ?_, ?_, fun x => ?_⟩
  · have := dual_ok n C.gates n (fun g' hg' => (hF g' hg').2) g hg
    exact ⟨by rcases this.1 with h | h <;> simp [h], this.2⟩
  · show (dual n n C.gates).length ≤ 2 * s
    rw [dual_len]
    have : C.gates.length ≤ s := hs
    omega
  · have hR0 : Rel n (List.ofFn x) (List.ofFn x ++ List.ofFn fun i => !x i) := by
      intro i hi
      have hi' : i < n := by simpa using hi
      unfold pw nw
      rw [if_pos hi', if_pos hi', List.getD_append _ _ _ _ (by simpa using hi'),
        List.getD_append_right _ _ _ _ (by simp)]
      have e1 := getD_ofFn x ⟨i, hi'⟩
      have e2 := getD_ofFn (fun i => !x i) ⟨i, hi'⟩
      simp only at e1 e2
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [e1, e2]
      simp
    have hR := dual_sim n C.gates n (List.ofFn x) _ (by simp) le_rfl (by simp; omega) hR0 hop
    rw [← hf x]
    show (wf (dual n n C.gates) (List.ofFn x ++ List.ofFn fun i => !x i)).getD _ false
      = (wf C.gates (List.ofFn x)).getD C.output false
    by_cases ho : C.output < n + C.gates.length
    · rw [if_pos ho]
      exact (hR C.output (by rw [wf_len]; simpa using ho)).1
    · rw [if_neg ho, List.getD_eq_default _ _ (by rw [wf_len, dual_len]; simp; omega),
        List.getD_eq_default _ _ (by rw [wf_len]; simp; omega)]



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp only [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem run_read (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [g.op.eval (g.inputs.map fun j => x.getD j false)])).getD i false = _
    rw [ih _ (by simp only [List.length_append]; omega), List.getD_append _ _ _ _ hi]

private theorem read_tail (a t : List Bool) (i : ℕ) :
    (a ++ t).getD (a.length + i) false = t.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private theorem read_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

private theorem mono_append {gs hs : List Gate}
    (hg : Monotone2 (⟨gs, 0⟩ : Circuit)) (hh : Monotone2 (⟨hs, 0⟩ : Circuit)) :
    Monotone2 (⟨gs ++ hs, 0⟩ : Circuit) := by
  intro g h
  exact (List.mem_append.mp h).elim (hg g) (hh g)

private def orGate (a b : ℕ) : Gate := ⟨.or, [a, b]⟩

private def chain (base acc : ℕ) : List ℕ → List Gate
  | [] => []
  | a :: as => orGate acc a :: chain (base + 1) base as

private def chainWire (base acc : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: as => base + as.length

private theorem chain_length (base acc : ℕ) (as : List ℕ) :
    (chain base acc as).length = as.length := by
  induction as generalizing base acc with
  | nil => rfl
  | cons a as ih => simp [chain, ih]

private theorem chain_mono (base acc : ℕ) (as : List ℕ) :
    Monotone2 (⟨chain base acc as, 0⟩ : Circuit) := by
  induction as generalizing base acc with
  | nil => simp [chain, Monotone2]
  | cons a as ih =>
    apply mono_append (gs := [orGate acc a]) (hs := chain (base + 1) base as)
    · simp [Monotone2, orGate]
    · exact ih _ _

private theorem chainWire_cons (base acc a : ℕ) (as : List ℕ) :
    chainWire base acc (a :: as) = chainWire (base + 1) base as := by
  cases as <;> simp [chainWire, Nat.add_comm, Nat.add_left_comm]

private theorem chainWire_lt (base acc : ℕ) (as : List ℕ) (hacc : acc < base) :
    chainWire base acc as < base + as.length := by
  cases as <;> simp [chainWire, hacc]

private theorem chain_value (x : List Bool) (acc : ℕ) (as : List ℕ)
    (ha : ∀ a ∈ as, a < x.length) :
    (run (chain x.length acc as) x).getD (chainWire x.length acc as) false =
      (x.getD acc false || as.any (fun a => x.getD a false)) := by
  induction as generalizing x acc with
  | nil => simp [run, Circuit.wires, chain, chainWire]
  | cons a as ih =>
    let value := x.getD acc false || x.getD a false
    let y := x ++ [value]
    have hlen : y.length = x.length + 1 := by simp [y]
    change (run ([orGate acc a] ++ chain (x.length + 1) x.length as) x).getD _ false = _
    rw [run_append, show run [orGate acc a] x = y by simp [run, Circuit.wires, orGate, GateOp.eval, y, value],
      chainWire_cons, ← hlen]
    rw [ih y x.length (fun j hj => by
      have := ha j (List.mem_cons_of_mem _ hj)
      omega)]
    have hv : y.getD x.length false = value := by simp [y]
    have hany : as.any (fun j => y.getD j false) = as.any (fun j => x.getD j false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      apply exists_congr
      intro j
      apply and_congr_right
      intro hj
      rw [show y.getD j false = x.getD j false from
        List.getD_append _ _ _ _ (ha j (List.mem_cons_of_mem _ hj))]
    rw [hv, hany, List.any_cons]
    exact Bool.or_assoc _ _ _

/-- Each task is the list of input wires for one OR. Its first wire seeds the chain. -/
private def batch (base : ℕ) : List (List ℕ) → List Gate
  | [] => []
  | as :: rs => chain base (as.headD 0) as.tail ++ batch (base + as.tail.length) rs

private def batchWire (base : ℕ) : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | as :: _, 0 => chainWire base (as.headD 0) as.tail
  | as :: rs, i + 1 => batchWire (base + as.tail.length) rs i

private theorem batch_length (base : ℕ) (rs : List (List ℕ)) :
    (batch base rs).length = (rs.map fun as => as.tail.length).sum := by
  induction rs generalizing base with
  | nil => rfl
  | cons as rs ih => simp [batch, chain_length, ih]

private theorem batch_mono (base : ℕ) (rs : List (List ℕ)) :
    Monotone2 (⟨batch base rs, 0⟩ : Circuit) := by
  induction rs generalizing base with
  | nil => simp [batch, Monotone2]
  | cons as rs ih => exact mono_append (chain_mono _ _ _) (ih _)

private theorem batch_spec (rs : List (List ℕ)) (base i : ℕ) (hi : i < rs.length)
    (hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base) :
    batchWire base rs i < base + (batch base rs).length ∧
      ∀ x : List Bool, x.length = base →
        (run (batch base rs) x).getD (batchWire base rs i) false =
          rs[i].any (fun j => x.getD j false) := by
  induction rs generalizing base i with
  | nil => simp at hi
  | cons as rs ih =>
    obtain ⟨hne, hvalid⟩ := hok as (by simp)
    cases as with
    | nil => exact (hne rfl).elim
    | cons a as =>
      let gs := chain base a as
      let hs := batch (base + as.length) rs
      have hg : gs.length = as.length := chain_length _ _ _
      have hd : batch base ((a :: as) :: rs) = gs ++ hs := rfl
      have htail (j : ℕ) (hj : j ∈ as) : j < base := hvalid j (List.mem_cons_of_mem _ hj)
      cases i with
      | zero =>
        have hw : chainWire base a as < base + gs.length := by
          rw [hg]
          exact chainWire_lt _ _ _ (hvalid a (by simp))
        refine ⟨by rw [hd, List.length_append]; change chainWire base a as < _; omega, ?_⟩
        intro x hx
        have hl : (run gs x).length = base + gs.length := by rw [run_length, hx]
        rw [hd, run_append]
        change (run hs (run gs x)).getD (chainWire base a as) false =
          (a :: as).any (fun j => x.getD j false)
        rw [run_read hs _ (hl ▸ hw)]
        simpa only [gs, hx, List.any_cons] using
          chain_value x a as (fun j hj => hx ▸ htail j hj)
      | succ i =>
        obtain ⟨hw, he⟩ := ih (base + as.length) i (by simpa using hi) (fun bs hb => by
          obtain ⟨hn, hb'⟩ := hok bs (List.mem_cons_of_mem _ hb)
          exact ⟨hn, fun j hj => Nat.lt_of_lt_of_le (hb' j hj) (Nat.le_add_right _ _)⟩)
        refine ⟨by simpa only [hd, List.length_append, hg, batchWire, List.tail_cons,
          Nat.add_assoc, hs] using hw, ?_⟩
        intro x hx
        have hl : (run gs x).length = base + as.length := by rw [run_length, hx, hg]
        rw [hd, run_append]
        change (run hs (run gs x)).getD (batchWire (base + as.length) rs i) false = _
        rw [he _ hl, List.getElem_cons_succ]
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        apply exists_congr
        intro j
        apply and_congr_right
        intro hj
        rw [run_read gs x (hx ▸ (hok _ (List.mem_cons_of_mem _ (List.getElem_mem _))).2 j hj)]

private theorem group_length {m n : ℕ} (base : ℕ) (f : Fin n → Fin m → ℕ) :
    (batch base (List.ofFn fun i => List.ofFn (f i))).length = n * (m - 1) := by
  rw [batch_length]
  have hmap : (List.ofFn (fun i => List.ofFn (f i))).map (fun as => as.tail.length) =
      List.replicate n (m - 1) := by
    rw [List.map_ofFn, ← List.ofFn_const]
    congr 1
    funext i
    simp
  rw [hmap, List.sum_replicate, Nat.nsmul_eq_mul]

private theorem buildGroups {m n : ℕ} (base : ℕ) (hm : 0 < m) (f : Fin n → Fin m → ℕ)
    (hf : ∀ i j, f i j < base) :
    ∃ (gs : List Gate) (w : Fin n → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length = n * (m - 1) ∧ (∀ i, w i < base + gs.length) ∧
      ∀ (x : List Bool), x.length = base → ∀ i,
        (run gs x).getD (w i) false = true ↔ ∃ j, x.getD (f i j) false = true := by
  let rs := List.ofFn fun i => List.ofFn (f i)
  have hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base := by
    intro as ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    refine ⟨?_, ?_⟩
    · intro h
      have hlen := congrArg List.length h
      simp [Nat.ne_of_gt hm] at hlen
    · intro j hj
      obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hj
      exact hf i r
  have hspec (i : Fin n) := batch_spec rs base i.val (by simp [rs]) hok
  refine ⟨batch base rs, fun i => batchWire base rs i.val, batch_mono _ _, group_length base f,
    fun i => (hspec i).1, ?_⟩
  intro x hx i
  rw [(hspec i).2 x hx, List.any_eq_true]
  simp only [rs, List.getElem_ofFn, List.mem_ofFn]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨_, ⟨j, rfl⟩, hj⟩

private def literalTask (n : ℕ) (f : ℕ → ℕ) (i : ℕ) (b : Bool) : List ℕ :=
  ((List.range n).filter fun j => decide (j.testBit i = b)).map f

private def bitTasks (n : ℕ) (f : ℕ → ℕ) : List ℕ → List (List ℕ)
  | [] => []
  | i :: is => literalTask n f i false :: literalTask n f i true :: bitTasks n f is

private theorem bitTasks_length (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) :
    (bitTasks n f is).length = 2 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [bitTasks, List.length_cons, ih]; omega

private theorem bitTasks_get (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) (i : ℕ)
    (hi : i < is.length) (b : Bool) :
    (bitTasks n f is)[2 * i + b.toNat]'(by rw [bitTasks_length]; cases b <;> simp <;> omega) =
      literalTask n f is[i] b := by
  induction is generalizing i with
  | nil => simp at hi
  | cons j is ih =>
    cases i with
    | zero => cases b <;> rfl
    | succ i =>
      have h : i < is.length := Nat.lt_of_succ_lt_succ hi
      have hs : 2 * (i + 1) + b.toNat = (2 * i + b.toNat) + 1 + 1 := by omega
      rw [getElem_congr_idx hs]
      simpa only [bitTasks, List.getElem_cons_succ] using ih i h

private theorem bitTasks_bound (n : ℕ) (f : ℕ → ℕ) (is : List ℕ) :
    ((bitTasks n f is).map fun as => as.tail.length).sum ≤ is.length * n := by
  induction is with
  | nil => simp [bitTasks]
  | cons i is ih =>
    have hp : (literalTask n f i false).length + (literalTask n f i true).length = n := by
      have hf : (fun j : ℕ => decide (j.testBit i = false)) = (fun j => !j.testBit i) := by
        funext j
        cases j.testBit i <;> rfl
      simp only [literalTask, List.length_map, hf, Bool.decide_eq_true]
      rw [Nat.add_comm, ← List.length_eq_length_filter_add, List.length_range]
    simp only [bitTasks, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
      List.length_tail] at *
    omega

private theorem buildBits (d base : ℕ) (f : ℕ → ℕ) (hf : ∀ j < 2 ^ d, f j < base) :
    ∃ (gs : List Gate) (w : Fin d → Bool → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length ≤ d * 2 ^ d ∧ (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : ℕ), x.length = base → u < 2 ^ d →
        (∀ j < 2 ^ d, x.getD (f j) false = decide (j = u)) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.testBit i = b) := by
  let n : ℕ := 2 ^ d
  let rs := bitTasks n f (List.range d)
  have hmem (as : List ℕ) (ha : as ∈ rs) : ∃ i < d, ∃ b, as = literalTask n f i b := by
    have haux (is : List ℕ) (h : as ∈ bitTasks n f is) :
        ∃ i ∈ is, ∃ b, as = literalTask n f i b := by
      induction is with
      | nil => simp [bitTasks] at h
      | cons i is ih =>
        rcases List.mem_cons.mp h with h | h
        · exact ⟨i, by simp, false, h⟩
        rcases List.mem_cons.mp h with h | h
        · exact ⟨i, by simp, true, h⟩
        obtain ⟨j, hj, b, hb⟩ := ih h
        exact ⟨j, List.mem_cons_of_mem _ hj, b, hb⟩
    simpa only [List.mem_range] using haux (List.range d) ha
  have hok : ∀ as ∈ rs, as ≠ [] ∧ ∀ j ∈ as, j < base := by
    intro as ha
    obtain ⟨i, hi, b, rfl⟩ := hmem as ha
    have hnon : ∃ j < n, j.testBit i = b := by
      cases b
      · exact ⟨0, Nat.two_pow_pos _, by simp⟩
      · exact ⟨2 ^ i, Nat.pow_lt_pow_right (by decide) hi, by simp⟩
    obtain ⟨j, hj, hb⟩ := hnon
    have hin : f j ∈ literalTask n f i b :=
      List.mem_map.mpr ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr hj, decide_eq_true hb⟩, rfl⟩
    refine ⟨fun he => by simp [he] at hin, ?_⟩
    intro r hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact hf _ (List.mem_range.mp (List.mem_filter.mp hq).1)
  have hspec (i : Fin d) (b : Bool) :=
    batch_spec rs base (2 * i.val + b.toNat) (by
      have hi := i.isLt
      simp only [rs, bitTasks_length, List.length_range]
      have hb : b.toNat < 2 := by cases b <;> decide
      omega) hok
  refine ⟨batch base rs, fun i b => batchWire base rs (2 * i.val + b.toNat), batch_mono _ _,
    ?_, fun i b => (hspec i b).1, ?_⟩
  · rw [batch_length]
    simpa only [rs, List.length_range] using bitTasks_bound n f (List.range d)
  intro x u hx hu hread i b
  rw [(hspec i b).2 x hx]
  have hget := bitTasks_get n f (List.range d) i.val (by simp) b
  simp only [List.getElem_range] at hget
  rw [hget]
  apply Bool.eq_iff_iff.mpr
  simp only [literalTask, List.any_map, List.any_eq_true, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Function.comp_apply]
  constructor
  · rintro ⟨j, ⟨hj, hb⟩, he⟩
    rw [hread j hj, decide_eq_true_eq] at he
    exact he ▸ hb
  · intro hb
    exact ⟨u, ⟨hu, hb⟩, by rw [hread u hu]; simp⟩

private theorem halfEncoder {m d : ℕ} (base : ℕ) (hm : 0 < m)
    (f : Fin (2 ^ d) → Fin m → ℕ) (hf : ∀ i j, f i j < base) :
    ∃ (gs : List Gate) (w : Fin d → Bool → ℕ), Monotone2 (⟨gs, 0⟩ : Circuit) ∧
      gs.length ≤ 2 ^ d * m + d * 2 ^ d ∧ (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : ℕ), x.length = base → u < 2 ^ d →
        (∀ i, (∃ j, x.getD (f i j) false = true) ↔ i.val = u) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.testBit i = b) := by
  obtain ⟨groups, g, hgm, hgl, hgr, hge⟩ := buildGroups base hm f hf
  let g' (j : ℕ) := if h : j < 2 ^ d then g ⟨j, h⟩ else 0
  obtain ⟨bits, w, hbm, hbl, hbr, hbe⟩ := buildBits d (base + groups.length) g' (by
    intro j hj
    simpa only [g', dite_eq_left hj] using hgr ⟨j, hj⟩)
  refine ⟨groups ++ bits, w, mono_append hgm hbm, ?_, ?_, ?_⟩
  · have hle := Nat.mul_le_mul_left (2 ^ d) (Nat.sub_le m 1)
    rw [List.length_append, hgl]
    omega
  · intro i b
    simpa only [List.length_append, Nat.add_assoc] using hbr i b
  · intro x u hx hu h i b
    rw [run_append]
    refine hbe _ u (by rw [run_length, hx]) hu (fun j hj => ?_) i b
    apply Bool.eq_iff_iff.mpr
    simp only [g', dite_eq_left hj, hge x hx, h, decide_eq_true_eq]

private theorem rectangle_lt {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.val + m * j.val < m * n := by
  calc
    i.val + m * j.val < m * (j.val + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ m * n := Nat.mul_le_mul_left _ j.isLt

private theorem rectangle_eq {m n : ℕ} (i : Fin m) (j : Fin n) (u : ℕ) :
    i.val + m * j.val = u ↔ i.val = u % m ∧ j.val = u / m := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  constructor
  · rintro rfl
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hm,
      Nat.mod_eq_of_lt i.isLt, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hi, hj⟩
    rw [hi, hj]
    exact Nat.mod_add_div _ _

private theorem buildEncoder (k base : ℕ) (xs : ℕ → ℕ)
    (hxs : ∀ j < 2 ^ k, xs j < base) :
    ∃ (gs : List Gate) (w : Fin k → Bool → ℕ),
      Monotone2 (⟨gs, 0⟩ : Circuit) ∧ gs.length ≤ 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) ∧
      (∀ i b, w i b < base + gs.length) ∧
      ∀ (x : List Bool) (u : Fin (2 ^ k)), x.length = base →
        (∀ j < 2 ^ k, x.getD (xs j) false = decide (j = u.val)) → ∀ i b,
        (run gs x).getD (w i b) false = decide (u.val.testBit i = b) := by
  let p := k / 2
  let q := (k + 1) / 2
  have hpq : p + q = k := by dsimp [p, q]; omega
  have hpow : 2 ^ p * 2 ^ q = (2 : ℕ) ^ k := by rw [← pow_add, hpq]
  have hle : (2 : ℕ) ^ p ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) (by dsimp [p, q]; omega)
  let f (i : Fin (2 ^ p)) (j : Fin (2 ^ q)) := xs (i.val + 2 ^ p * j.val)
  have hrect (i : Fin (2 ^ p)) (j : Fin (2 ^ q)) : i.val + 2 ^ p * j.val < 2 ^ k := by
    rw [← hpow]
    exact rectangle_lt i j
  obtain ⟨lo, wlo, hloM, hloS, hloR, hloE⟩ :=
    halfEncoder base (Nat.two_pow_pos q) f (fun i j => hxs _ (hrect i j))
  obtain ⟨hi, whi, hhiM, hhiS, hhiR, hhiE⟩ :=
    halfEncoder (base + lo.length) (Nat.two_pow_pos p) (fun j i => f i j) (fun j i =>
      Nat.lt_of_lt_of_le (hxs _ (hrect i j)) (Nat.le_add_right _ _))
  let w (i : Fin k) (b : Bool) := if h : i.val < p then wlo ⟨i.val, h⟩ b
    else whi ⟨i.val - p, by have := i.isLt; omega⟩ b
  refine ⟨lo ++ hi, w, mono_append hloM hhiM, ?_, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left p hle
    rw [Nat.mul_comm (2 ^ q) (2 ^ p), hpow] at hhiS
    rw [hpow] at hloS
    rw [List.length_append]
    change _ ≤ 2 * 2 ^ k + k * 2 ^ q
    rw [← hpq, Nat.add_mul, hpq]
    omega
  · intro i b
    unfold w
    split
    · have := hloR ⟨i.val, ‹i.val < p›⟩ b
      simp only [List.length_append]
      omega
    · simpa only [List.length_append, Nat.add_assoc] using hhiR _ b
  · intro x u hx hread i b
    have hmod : u.val % 2 ^ p < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
    have hdiv : u.val / 2 ^ p < 2 ^ q := by
      apply Nat.div_lt_of_lt_mul
      rw [hpow]
      exact u.isLt
    have hclass (a : Fin (2 ^ p)) (c : Fin (2 ^ q)) :
        x.getD (f a c) false = true ↔ a.val = u.val % 2 ^ p ∧ c.val = u.val / 2 ^ p := by
      change x.getD (xs (a.val + 2 ^ p * c.val)) false = true ↔ _
      rw [hread _ (hrect a c), decide_eq_true_eq, rectangle_eq a c]
    have hlo (a : Fin (2 ^ p)) :
        (∃ c, x.getD (f a c) false = true) ↔ a.val = u.val % 2 ^ p := by
      simp only [hclass]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⟨_, hdiv⟩, h, rfl⟩⟩
    have hloLen : (run lo x).length = base + lo.length := by rw [run_length, hx]
    have hhi (c : Fin (2 ^ q)) :
        (∃ a, (run lo x).getD (f a c) false = true) ↔ c.val = u.val / 2 ^ p := by
      have hread' (a : Fin (2 ^ p)) :
          (run lo x).getD (f a c) false = x.getD (f a c) false :=
        run_read lo x (by rw [hx]; exact hxs _ (hrect a c))
      simp only [hread', hclass]
      exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨⟨_, hmod⟩, rfl, h⟩⟩
    rw [run_append]
    unfold w
    split
    · rename_i h
      rw [run_read hi _ (hloLen ▸ hloR ⟨i.val, h⟩ b), hloE x _ hx hmod hlo,
        Nat.testBit_mod_two_pow]
      simp [h]
    · rename_i h
      rw [hhiE _ _ hloLen hdiv hhi, Nat.testBit_div_two_pow]
      have heq : i.val - p + p = i.val := by omega
      simp only [heq]

private def liftWire (n base limit : ℕ) (w : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then w ⟨i, h⟩ else base + min (i - n) limit

private def liftGate (n base limit : ℕ) (w : Fin n → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftWire n base limit w)⟩

private theorem run_lift {n base limit : ℕ} {w : Fin n → ℕ} {x y : List Bool}
    (hx : x.length = n) (hy : y.length = base) (hw : ∀ i, w i < base)
    (hread : ∀ i, y.getD (w i) false = x.getD i.val false)
    (gs : List Gate) (t : List Bool) (ht : t.length + gs.length ≤ limit) (i : ℕ) :
    (run (gs.map (liftGate n base limit w)) (y ++ t)).getD (liftWire n base limit w i) false =
      (run gs (x ++ t)).getD i false := by
  have reads (t : List Bool) (hlen : t.length ≤ limit) (j : ℕ) :
      (y ++ t).getD (liftWire n base limit w j) false = (x ++ t).getD j false := by
    unfold liftWire
    split
    · rename_i hj
      rw [List.getD_append _ _ _ _ (hy ▸ hw ⟨j, hj⟩),
        List.getD_append _ _ _ _ (hx ▸ hj)]
      exact hread ⟨j, hj⟩
    · rename_i hj
      rw [← hy, read_tail, List.getD_append_right _ _ _ _ (by omega), hx]
      by_cases h : j - n ≤ limit
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
  induction gs generalizing t with
  | nil => exact reads t (by simpa using ht) i
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun j => (x ++ t).getD j false)
    have ht' : t.length ≤ limit := by omega
    have hz : g.op.eval (g.inputs.map ((fun j => (y ++ t).getD j false) ∘
        liftWire n base limit w)) = z := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro j _
      exact reads t ht' j
    change (run (gs.map (liftGate n base limit w))
      ((y ++ t) ++ [g.op.eval (((g.inputs.map (liftWire n base limit w)).map
        fun j => (y ++ t).getD j false))])).getD _ false =
        (run gs ((x ++ t) ++ [z])).getD i false
    simp only [List.map_map, hz, List.append_assoc]
    apply ih (t ++ [z])
    simp only [List.length_append, List.length_cons, List.length_nil] at *
    omega

private theorem tableIndex_decodes (k u : ℕ) (hu : u < 2 ^ k) :
    tableIndex (fun i : Fin k => u.testBit i) = u := by
  induction k generalizing u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    simp [tableIndex, hz]
  | succ k ih =>
    have hd : u / 2 < 2 ^ k := by
      rw [pow_succ] at hu
      omega
    unfold tableIndex
    rw [Fin.sum_univ_succ]
    have hsum : (∑ i : Fin k, if u.testBit (i.succ.val) = true then 2 ^ (i.succ.val) else 0) =
        2 * tableIndex (fun i : Fin k => (u / 2).testBit i) := by
      rw [tableIndex, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, ← Nat.testBit_div_two, pow_succ]
      split <;> simp [Nat.mul_comm]
    rw [hsum, ih _ hd]
    simp only [Fin.val_zero, pow_zero, Nat.testBit_zero, decide_eq_true_eq]
    split <;> omega

private def joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) : Fin (k + l) → α :=
  Fin.addCases f g

private theorem ofFn_joinFin {k l : ℕ} {α : Type} (f : Fin k → α) (g : Fin l → α) :
    List.ofFn (joinFin f g) = List.ofFn f ++ List.ofFn g := by
  rw [List.ofFn_add]
  have hl (i : Fin k) : joinFin f g (Fin.castLE (Nat.le_add_right k l) i) = f i :=
    Fin.addCases_left i
  have hr (i : Fin l) : joinFin f g (Fin.natAdd k i) = g i := Fin.addCases_right i
  simp only [hl, hr]

private theorem bitGraph {k l : ℕ} (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (u : Fin (2 ^ k)) (v : Fin (2 ^ l)) :
    adjFun A (joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)) =
      A u v := by
  simp only [adjFun, joinFin, Fin.addCases_left, Fin.addCases_right,
    tableIndex_decodes k u.val u.isLt, tableIndex_decodes l v.val v.isLt]
  congr 1
  · apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt
  · apply Fin.ext
    exact Nat.mod_eq_of_lt v.isLt

private theorem assemble (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool)
    (h : HasLitSize (k + l) (adjFun A) s) :
    RepSizeAtMost A (s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2)) := by
  obtain ⟨C, hCm, hCs, hCe⟩ := h
  let base : ℕ := 2 ^ k + 2 ^ l
  obtain ⟨gsL, wL, hmL, hsL, hwL, heL⟩ :=
    buildEncoder k base id (fun _ hj => Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _))
  obtain ⟨gsR, wR, hmR, hsR, hwR, heR⟩ :=
    buildEncoder l (base + gsL.length) (fun j => 2 ^ k + j) (fun j hj => by dsimp [base]; omega)
  let endL := base + gsL.length
  let endR := endL + gsR.length
  let w (b : Bool) := joinFin (fun i => wL i b) (fun j => wR j b)
  let litW := joinFin (w true) (w false)
  let n := (k + l) + (k + l)
  let gs := C.gates.map (liftGate n endR C.gates.length litW)
  have hgm : Monotone2 (⟨gs, 0⟩ : Circuit) := by
    intro g hg
    change g ∈ C.gates.map (liftGate n endR C.gates.length litW) at hg
    obtain ⟨orig, hOrig, hEq⟩ := List.mem_map.mp hg
    rw [← hEq]
    simpa only [liftGate, List.length_map] using hCm orig hOrig
  refine ⟨⟨gsL ++ gsR ++ gs, liftWire n endR C.gates.length litW C.output⟩,
    mono_append (mono_append hmL hmR) hgm, ?_, ?_⟩
  · change C.gates.length ≤ s at hCs
    simp only [Circuit.size, List.length_append, gs, List.length_map]
    omega
  intro u v
  let a := oneEach u v
  let aL := run gsL a
  let aR := run gsR aL
  have ha : a.length = base := by simp [a, base, oneEach]
  have haL : aL.length = endL := by simp only [aL, run_length, ha, endL]
  have haR : aR.length = endR := by simp only [aR, run_length, haL, endR]
  have inL (j : ℕ) (hj : j < 2 ^ k) : a.getD (id j) false = decide (j = u.val) := by
    have hleft : j < (List.ofFn (fun i : Fin (2 ^ k) => decide (i = u))).length := by simp [hj]
    simp only [a, oneEach, id_eq]
    rw [List.getD_append _ _ _ _ hleft]
    exact (read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff)
  have inR (j : ℕ) (hj : j < 2 ^ l) : aL.getD (2 ^ k + j) false = decide (j = v.val) := by
    change (run gsL a).getD (2 ^ k + j) false = _
    rw [run_read gsL _ (by rw [ha]; dsimp [base]; omega)]
    have ht := read_tail (List.ofFn fun i : Fin (2 ^ k) => decide (i = u))
      (List.ofFn fun i : Fin (2 ^ l) => decide (i = v)) j
    simp only [List.length_ofFn] at ht
    exact ht.trans ((read_ofFn _ ⟨j, hj⟩).trans (decide_eq_decide.mpr Fin.ext_iff))
  let x := joinFin (fun i : Fin k => u.val.testBit i) (fun j : Fin l => v.val.testBit j)
  have hwl (i : Fin k) (b : Bool) : wL i b < aL.length := haL ▸ hwL i b
  have hbound₁ (i : Fin (k + l)) (b : Bool) : w b i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hb := hwL j b
      simp only [w, joinFin, Fin.addCases_left, endR, endL]
      omega
    · simpa only [w, joinFin, Fin.addCases_right, endR, endL] using hwR j b
  have hbound (i : Fin n) : litW i < endR := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [litW, joinFin, Fin.addCases_left] using hbound₁ j true
    · simpa only [litW, joinFin, Fin.addCases_right] using hbound₁ j false
  have hlit (i : Fin (k + l)) (b : Bool) : aR.getD (w b i) false = decide (x i = b) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [w, x, joinFin, Fin.addCases_left, aR]
      rw [run_read gsR _ (hwl j b)]
      exact heL a u ha inL j b
    · simp only [w, x, joinFin, Fin.addCases_right]
      exact heR aL v haL inR j b
  let litX := joinFin x (fun i => !x i)
  have hx : List.ofFn litX = List.ofFn x ++ List.ofFn (fun i => !x i) := ofFn_joinFin _ _
  have hread (i : Fin n) : aR.getD (litW i) false = (List.ofFn litX).getD i.val false := by
    rw [read_ofFn]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [litW, litX, joinFin, Fin.addCases_left, hlit]
      cases x j <;> rfl
    · simp only [litW, litX, joinFin, Fin.addCases_right, hlit]
      cases x j <;> rfl
  change (run (gsL ++ gsR ++ gs) a).getD _ false = A u v
  simp only [run_append]
  change (run gs aR).getD _ false = A u v
  have hlift := run_lift (limit := C.gates.length) (x := List.ofFn litX) (y := aR)
    List.length_ofFn haR hbound hread C.gates [] (by simp) C.output
  simp only [List.append_nil] at hlift
  rw [hlift]
  change C.eval (List.ofFn litX) = A u v
  rw [hx, hCe]
  exact bitGraph A u v



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem tpoly_le (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hi')

theorem tp4 (l : ℕ) (hl : 16 ≤ l) : l ^ 4 ≤ 2 ^ l := by
  induction l, hl using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 16 * n ≤ n ^ 2 := by nlinarith
    have h3 : 16 * n ^ 2 ≤ n ^ 3 := by nlinarith
    have h4 : 16 * n ^ 3 ≤ n ^ 4 := by nlinarith
    have : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
      have e : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
      rw [e]; omega
    calc (n + 1) ^ 4 ≤ 2 * n ^ 4 := this
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (n + 1) := by ring

theorem tpbound (p : Polynomial ℕ) (K : ℕ) : ∃ k, K ≤ k ∧ 2 * p.eval (2 * k) ≤ 2 ^ k := by
  obtain ⟨Cs, hCs⟩ : ∃ c, c = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = p.natDegree := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 4 * (Cs + 1) * (d + 1) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = max K B + 16 := ⟨_, rfl⟩
  have hqK : K ≤ q := by omega
  have hqB : B ≤ q := by omega
  have hq16 : 16 ≤ q := by omega
  have hdq : q ≤ (d + 1) * q := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(d + 1) * q, by omega, ?_⟩
  have hk1 : 1 ≤ 2 * ((d + 1) * q) := by omega
  have h1 := tpoly_le p (2 * ((d + 1) * q)) hk1
  rw [← hCs, ← hd] at h1
  have h2 : (2 * ((d + 1) * q)) ^ d ≤ (2 * ((d + 1) * q)) ^ (d + 1) :=
    Nat.pow_le_pow_right hk1 (by omega)
  have h3 : 2 * Cs ≤ (2 * (Cs + 1)) ^ (d + 1) :=
    le_trans (by omega) (Nat.le_self_pow (by omega) _)
  have h4 : 2 * (Cs + 1) * (2 * ((d + 1) * q)) = B * q := by rw [hB]; ring
  have h5 : B * q ≤ 2 ^ q := by
    calc B * q ≤ q * q := Nat.mul_le_mul_right _ hqB
      _ = q ^ 2 := (sq q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ 2 ^ q := tp4 q hq16
  calc 2 * p.eval (2 * ((d + 1) * q)) ≤ 2 * (Cs * (2 * ((d + 1) * q)) ^ d) :=
        Nat.mul_le_mul_left _ h1
    _ ≤ 2 * Cs * (2 * ((d + 1) * q)) ^ (d + 1) := by
        rw [← Nat.mul_assoc 2 Cs]; exact Nat.mul_le_mul_left _ h2
    _ ≤ (2 * (Cs + 1)) ^ (d + 1) * (2 * ((d + 1) * q)) ^ (d + 1) := Nat.mul_le_mul_right _ h3
    _ = (B * q) ^ (d + 1) := by rw [← mul_pow, h4]
    _ ≤ (2 ^ q) ^ (d + 1) := Nat.pow_le_pow_left h5 _
    _ = 2 ^ ((d + 1) * q) := by rw [← pow_mul, mul_comm]

theorem tadj_cast (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (y : List Bool) (m k : ℕ)
    (h : m = k) :
    PEqualNP.Represents.adjFun (k := m) (l := m) (A m) (fun i => y.getD i false) =
      PEqualNP.Represents.adjFun (k := k) (l := k) (A k) (fun i => y.getD i false) := by
  subst h; rfl

theorem tpbound2 (p : Polynomial ℕ) (d K : ℕ) :
    ∃ m, K ≤ m ∧ 8 * d * p.eval (2 * (2 * m)) + 64 * d * m ≤ 2 ^ m := by
  obtain ⟨m, hKm, hm⟩ := tpbound
    (Polynomial.C (4 * d) * p.comp (Polynomial.C 2 * Polynomial.X) +
      Polynomial.C (16 * d) * Polynomial.X) K
  refine ⟨m, hKm, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_comp] at hm
  have e : 2 * (4 * d * p.eval (2 * (2 * m)) + 16 * d * (2 * m)) =
      8 * d * p.eval (2 * (2 * m)) + 64 * d * m := by ring
  rw [e] at hm
  exact hm

theorem tarith (m d s : ℕ) (hd : 0 < d) (hpm : 8 * d * s + 64 * d * m ≤ 2 ^ m) :
    2 * s + 2 * 2 ^ (2 * m) + 2 * m * 2 ^ ((2 * m + 1) / 2) + 2 * 2 ^ (2 * m) +
      2 * m * 2 ^ ((2 * m + 1) / 2) ≤ 4 * 2 ^ (2 * m) + 2 ^ (2 * m) / d := by
  have hh : (2 * m + 1) / 2 = m := by omega
  have hp2 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [hh, hp2]
  obtain ⟨a, ha⟩ : ∃ a, a = 2 ^ m := ⟨_, rfl⟩
  rw [← ha]
  rw [← ha] at hpm
  have ha1 : 1 ≤ a := by rw [ha]; exact Nat.one_le_two_pow
  have h1 : (8 * d * s + 64 * d * m) * a ≤ a * a := Nat.mul_le_mul_right a hpm
  have h2 : d * s ≤ d * s * a := Nat.le_mul_of_pos_right _ ha1
  have hq : 2 * s + 2 * m * a + 2 * m * a ≤ a * a / d := by
    rw [Nat.le_div_iff_mul_le hd]
    have e1 : (2 * s + 2 * m * a + 2 * m * a) * d = 2 * (d * s) + 4 * (d * m * a) := by ring
    have e2 : (8 * d * s + 64 * d * m) * a = 8 * (d * s * a) + 64 * (d * m * a) := by ring
    rw [e1]
    rw [e2] at h1
    omega
  omega

theorem main12318 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hconv A d K hd hA hL hsub
  obtain ⟨p, hp⟩ := hsub hL
  simp only [PEqualNP.CircuitLowerBounds.SIZE] at hp
  obtain ⟨m, hKm, hpm⟩ := tpbound2 p d K
  apply hA (2 * m) (by omega)
  obtain ⟨C, hCg, hCs, hCd⟩ := hp (2 * (2 * m))
  have hHC : HasCircuitSize (2 * m + 2 * m) (PEqualNP.Represents.adjFun (A (2 * m)))
      (p.eval (2 * (2 * m))) := by
    refine ⟨C, hCg, hCs, ?_⟩
    intro x
    have hlen : (List.ofFn x).length = 2 * (2 * m) := by rw [List.length_ofFn]; ring
    have hd := hCd (List.ofFn x) hlen
    rw [Bool.eq_iff_iff, hd]
    have hfx : (fun i : Fin (2 * m + 2 * m) => (List.ofFn x).getD i false) = x := by
      funext i; exact ofFn_getD x i i.isLt
    have key : PEqualNP.Represents.adjFun (k := (List.ofFn x).length / 2)
        (l := (List.ofFn x).length / 2) (A ((List.ofFn x).length / 2))
        (fun i => (List.ofFn x).getD i false) = PEqualNP.Represents.adjFun (A (2 * m)) x := by
      rw [tadj_cast A (List.ofFn x) ((List.ofFn x).length / 2) (2 * m) (by rw [hlen]; omega), hfx]
    constructor
    · intro h
      obtain ⟨_, h2⟩ := h
      exact key.symm.trans h2
    · intro h
      exact And.intro (by rw [hlen]; exact even_two_mul (2 * m)) (key.trans h)
  obtain ⟨D, hD1, hD2, hD3⟩ := hconv (2 * m) (2 * m) _ (A (2 * m)) hHC
  refine ⟨D, hD1, le_trans hD2 ?_, hD3⟩
  exact tarith m d _ hd hpm


theorem main16079 : ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro A d K hd hA hL
  exact main12318 (fun k l s A h => assemble k l (2 * s) A (conv9020 _ _ _ h)) A d K hd hA hL

theorem main_aux : ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → PEqualNP.Library.P ≠ PEqualNP.Library.NP := by
  intro A d K hd hA hL hPNP
  apply main16079 A d K hd hA hL
  rw [hPNP.symm]
  exact libL006

end PEqualNP.Outside.L_meta_16080

theorem PEqualNP.Outside.L_meta_16080 : ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → PEqualNP.Library.P ≠ PEqualNP.Library.NP :=
  PEqualNP.Outside.L_meta_16080.main_aux
