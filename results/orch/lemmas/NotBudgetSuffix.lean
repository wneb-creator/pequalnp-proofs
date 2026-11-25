
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

lemma flipRef_false (r : WireRef) : flipRef false r = r := by
  rcases r with c | ⟨i,p⟩ <;> simp [flipRef]

lemma state_append {phase : List Bool} {marks : Finset ℕ} {env : List WireRef}
    {gs : List U2Gate} {r : WireRef} (h : StateGood phase marks env gs)
    (hr : RefGood phase marks r) : StateGood phase marks (env ++ [r]) gs := by
  refine ⟨h.1, ?_⟩
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h.2 s hs
  · simpa only [List.mem_singleton.mp hs] using hr

lemma binary_good {phase : List Bool} {marks : Finset ℕ} {gs : List U2Gate}
    {ea eb : WireRef} (p : Bool) (hg : GatesGood phase marks gs)
    (ha : RefGood phase marks ea) (hb : RefGood phase marks eb) :
    let res := evalAndRef (flipRef p ea) (flipRef p eb) gs
    ∃ phase', GatesGood phase' marks res.2 ∧
      (∀ r, RefGood phase marks r → RefGood phase' marks r) ∧
      RefGood phase' marks (flipRef p res.1) := by
  rcases ea with ca | ⟨wa,fa⟩ <;> rcases eb with cb | ⟨wb,fb⟩
  · cases p <;> cases ca <;> cases cb <;>
      exact ⟨phase,hg,fun _ h => h, trivial⟩
  · cases p <;> cases ca <;>
      refine ⟨phase, ?_, fun _ h => h, ?_⟩ <;>
      simp_all [flipRef, evalAndRef, RefGood]
  · cases p <;> cases cb <;>
      refine ⟨phase, ?_, fun _ h => h, ?_⟩ <;>
      simp_all [flipRef, evalAndRef, RefGood]
  · refine ⟨phase ++ [p], ?_, fun _ h => refGood_snoc p h, ?_⟩
    · exact (append_gate p hg ha hb).1
    · simpa [flipRef, evalAndRef] using (append_gate p hg ha hb).2

lemma state_binary {phase : List Bool} {marks : Finset ℕ} {gs : List U2Gate}
    {env : List WireRef} (p : Bool) (h : StateGood phase marks env gs) (u v : ℕ) :
    let res := evalAndRef (flipRef p (env.getD u (Sum.inl false)))
      (flipRef p (env.getD v (Sum.inl false))) gs
    ∃ phase', StateGood phase' marks (env ++ [flipRef p res.1]) res.2 := by
  obtain ⟨phase',hg,he,ho⟩ := binary_good p h.1 (env_getD_good h.2 u) (env_getD_good h.2 v)
  refine ⟨phase', state_append ⟨hg, ?_⟩ ho⟩
  exact fun r hr => he r (h.2 r hr)

lemma step_budget {phase : List Bool} {marks : Finset ℕ} {gs : List U2Gate}
    {env : List WireRef} (h : StateGood phase marks env gs) (g : Gate) :
    let res := toU2Step env gs g
    ∃ phase' marks', StateGood phase' marks' res.1 res.2 ∧
      marks'.card ≤ marks.card + notCount ⟨[g],0⟩ := by
  rcases g with ⟨op,ins⟩
  cases op with
  | and =>
    cases ins with
    | nil => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
    | cons u us =>
      cases us with
      | nil => exact ⟨phase,marks,state_append h (env_getD_good h.2 u),by simp [notCount]⟩
      | cons v vs =>
        cases vs with
        | nil =>
          obtain ⟨phase',h'⟩ := state_binary false h u v
          refine ⟨phase',marks,?_,by simp [notCount]⟩
          simpa only [toU2Step, flipRef_false] using h'
        | cons w ws => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
  | or =>
    cases ins with
    | nil => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
    | cons u us =>
      cases us with
      | nil => exact ⟨phase,marks,state_append h (env_getD_good h.2 u),by simp [notCount]⟩
      | cons v vs =>
        cases vs with
        | nil =>
          obtain ⟨phase',h'⟩ := state_binary true h u v
          exact ⟨phase',marks,h',by simp [notCount]⟩
        | cons w ws => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
  | not =>
    cases ins with
    | nil => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
    | cons u us =>
      have hu := env_getD_good h.2 u
      cases hr : env.getD u (Sum.inl false) with
      | inl c =>
        refine ⟨phase,marks,?_,by simp [notCount]⟩
        change StateGood phase marks (env ++ [flipRef true (env.getD u (Sum.inl false))]) gs
        rw [hr]
        exact state_append h trivial
      | inr r =>
        rcases r with ⟨i,p⟩
        have hm : marks ⊆ insert i marks := Finset.subset_insert i marks
        have hg := gatesGood_mono hm h.1
        have he : ∀ r ∈ env, RefGood phase (insert i marks) r :=
          fun r hr => refGood_mono hm (h.2 r hr)
        rw [hr] at hu
        refine ⟨phase,insert i marks,?_,?_⟩
        · change StateGood phase (insert i marks) (env ++ [flipRef true (env.getD u (Sum.inl false))]) gs
          rw [hr]
          exact state_append ⟨hg,he⟩ (refGood_flip_mark hu)
        · simpa [notCount] using Finset.card_insert_le i marks
  | mod m => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩
  | maj => exact ⟨phase,marks,state_append h trivial,by simp [notCount]⟩

end PEqualNP.Outside.L_meta_2592_aux.NotBudget
