import WeakCompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
namespace Compact
open Resolution

theorem Layout.exact_from_chain {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x i : V) (P : Nat)
    (xp : x ∈ mask P) (ix : adj i x)
    (wit : ∃ q s, q < D.length ∧ tag D q = true ∧
      sem_Chain 14 D i.val (src D (q, !s)) ∧
      ∀ a ∈ mask P, a ∈ supp 14 D (src D (q, s)) ↔ adj i a) :
    ∃ j < cap k I x, Z.see x i P j := by
  obtain ⟨q, s, hq, ht, chain, ex⟩ := wit
  have mem : (q, s) ∈ sem_W 14 D x := by
    refine sem_mem_W.mpr ⟨hq, (ex _ xp).2 ix, ?_⟩
    intro hx
    have pure := sem_dom_pure graph_ok h.1 hc i _ (sem_chain_dom h.1 chain)
    have eq := Finset.mem_singleton.mp (pure (sem_supp_and_sub h.1 hq ht (!s) hx))
    exact graph_ok.2.1 i (eq ▸ ix)
  obtain ⟨j, live, same⟩ := Z.covers x (q, s) mem
  exact ⟨j, lt_of_lt_of_le live (Z.limit x), live,
    fun c cp => by simpa [Layout.lab, SLabel, same] using ex c cp⟩

theorem Layout.paired_exact {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (x i y j : V) (P : Nat)
    (geom : independent (mask P) ∧ i ∈ mask I ∧ j ∈ mask I ∧
      x ∈ mask P ∧ y ∈ mask P ∧ adj i x ∧ adj j y ∧
      ∃ a ∈ mask P, adj j a ∧ ¬adj i a) :
    (∃ r < cap k I x, Z.see x i P r) ∨
      ∃ r < cap k I y, Z.see y j P r := by
  obtain ⟨ind, hi, hj, xp, yp, ix, jy, diff⟩ := geom
  rcases sem_shared_empty graph_ok h hc z (mask P) ind (eq ▸ hi) (eq ▸ hj) diff with wi | wj
  · exact Or.inl (Z.exact_from_chain h hc x i P xp ix wi)
  · exact Or.inr (Z.exact_from_chain h hc y j P yp jy wj)

inductive BudgetScheme where
  | plain (q : Scheme)
  | pairedExact (x i y j : V) (p : Nat)

def enabledBudget (k I : Nat) : BudgetScheme → Bool
  | .plain q => weakScheme q && enabled k I q
  | .pairedExact x i y j p => decide (independent (mask p) ∧
      i ∈ mask I ∧ j ∈ mask I ∧ x ∈ mask p ∧ y ∈ mask p ∧
      adj i x ∧ adj j y ∧ ∃ a ∈ mask p, adj j a ∧ ¬adj i a)

def expandBudget (k I : Nat) : BudgetScheme → FactClause
  | .plain q => expand k I q
  | .pairedExact x i y j p =>
      anyRange (cap k I x) (fun r => .see x i p r) ++
      anyRange (cap k I y) (fun r => .see y j p r)

theorem scheme_sound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (q : BudgetScheme)
    (en : enabledBudget k I q = true) : EvalClause Z (expandBudget k I q) := by
  cases q with
  | plain q =>
    simp only [enabledBudget, Bool.and_eq_true] at en
    exact scheme_sound_weak Z h hc eq q en.1 en.2
  | pairedExact x i y j p =>
    have geo := of_decide_eq_true en
    have hh := Z.paired_exact h hc z eq x i y j p geo
    rcases hh with hx | hy
    · obtain ⟨f, hf, yes⟩ := (range_iff Z (cap k I x) (fun r => Fact.see x i p r)).mpr hx
      exact ⟨f, List.mem_append_left _ hf, yes⟩
    · obtain ⟨f, hf, yes⟩ := (range_iff Z (cap k I y) (fun r => Fact.see y j p r)).mpr hy
      exact ⟨f, List.mem_append_right _ hf, yes⟩

def localCheckBudget (k I : Nat) (a : Array Fact) (r : BudgetScheme) (c : Clause) : Bool :=
  enabledBudget k I r && (expandBudget k I r).all (fun p => (c.map (atLit a)).contains p)

def inputsOKBudget (k I : Nat) (a : Array Fact) : List BudgetScheme → List Clause → Bool
  | [], [] => true
  | r::rs, c::cs => localCheckBudget k I a r c && inputsOKBudget k I a rs cs
  | _, _ => false

theorem localSound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (a : Array Fact) (r : BudgetScheme)
    (c : Clause) (ok : localCheckBudget k I a r c = true) : Holds (truth Z a) c := by
  simp only [localCheckBudget, Bool.and_eq_true] at ok
  obtain ⟨p, hm, hval⟩ := scheme_sound_budget Z h hc z eq r ok.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2 p hm)
  obtain ⟨l, hl, eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l, hl, ?_⟩
  rcases l with ⟨i, b⟩
  cases b <;> simp [truth, Yes, atLit] at hval ⊢ <;> exact hval

theorem inputs_sound_budget {D : Dag} {k I : Nat} (Z : Layout D k I)
    (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1)
    (eq : mask I = ineligSet 14 D) (a : Array Fact) (R : List BudgetScheme)
    (F : Array Clause) (ok : inputsOKBudget k I a R F.toList = true) : Valid (truth Z a) F := by
  have all (rs : List BudgetScheme) (cs : List Clause)
      (good : inputsOKBudget k I a rs cs = true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOKBudget, List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOKBudget, Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl | rest
        · exact localSound_budget Z h hc z eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)

theorem book_start_budget {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D ≤ 1) (eq : mask I = ineligSet 14 D)
    (a : Array Fact) (R : List BudgetScheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOKBudget k I a R (baseBook book n).toList = true) :
    ValidThrough (truth Z a) book n := by
  have sat := inputs_sound_budget Z h hc z eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j, hj⟩, rfl⟩

end Compact
end PEqualNP.Outside.L_meta_9775.UpstreamCore
