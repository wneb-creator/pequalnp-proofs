import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0
  | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 5 | _ => 6

def witness0 (v : Fin 10) : Fin 10 → Bool := fun i => decide (i = neighbor v)

def witness1 (v : Fin 10) : Fin 10 → Bool := fun i => decide (i = v ∨ i = neighbor v)

lemma witness_agree (v i : Fin 10) (h : i ≠ v) : witness0 v i = witness1 v i := by
  simp [witness0, witness1, h]

lemma witness_seed : ∀ v : Fin 10,
    (witness0 v 0 && witness0 v 2) = (witness1 v 0 && witness1 v 2) := by
  decide

lemma witness_target : ∀ v : Fin 10, target (witness0 v) = false ∧ target (witness1 v) = true := by
  decide

lemma inputMap_surjective (σ : Fin 10 → Fin 10) (F : List Bool → Bool)
    (h : ∀ x : Fin 10 → Bool,
      F (List.ofFn (x ∘ σ) ++ [x 0 && x 2]) = target x) : Function.Surjective σ := by
  classical
  intro v
  apply Classical.byContradiction
  intro hn
  have hσ : ∀ i, σ i ≠ v := fun i hi => hn ⟨i, hi⟩
  have he : witness0 v ∘ σ = witness1 v ∘ σ := by
    funext i
    exact witness_agree v (σ i) (hσ i)
  have heinput :
      List.ofFn (witness0 v ∘ σ) ++ [witness0 v 0 && witness0 v 2] =
      List.ofFn (witness1 v ∘ σ) ++ [witness1 v 0 && witness1 v 2] := by
    rw [he, witness_seed]
  have hc := congrArg F heinput
  rw [h, h] at hc
  have hw := witness_target v
  rw [hw.1, hw.2] at hc
  cases hc

lemma nonSurjective_counterinput (σ : Fin 10 → Fin 10) (F : List Bool → Bool)
    (hσ : ¬ Function.Surjective σ) :
    ∃ x : Fin 10 → Bool, F (List.ofFn (x ∘ σ) ++ [x 0 && x 2]) ≠ target x := by
  apply Classical.byContradiction
  intro h
  apply hσ
  apply inputMap_surjective σ F
  intro x
  apply Classical.byContradiction
  intro hx
  exact h ⟨x, hx⟩

def pinWitness (u w : Fin 10) (b : Bool) : Fin 10 → Bool :=
  Function.update (fun i => decide (i = w)) u b

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma target_restriction_witness : ∀ (u v : Fin 10) (b : Bool), u ≠ v →
    ∃ w : Fin 10, w ≠ u ∧ w ≠ v ∧
      target (pinWitness u w b) = false ∧
      target (Function.update (pinWitness u w b) v true) = true := by
  decide

lemma restricted_sensitive (u v : Fin 10) (h : u ≠ v) (b : Bool) :
    ∃ x : Fin 10 → Bool, x u = b ∧ x v = false ∧ target x = false ∧
      target (Function.update x v true) = true := by
  obtain ⟨w, hwu, hwv, ht0, ht1⟩ := target_restriction_witness u v b h
  refine ⟨pinWitness u w b, ?_, ?_, ht0, ht1⟩
  · simp [pinWitness]
  · simp [pinWitness, Function.update_of_ne h.symm, hwv.symm]

lemma no_pair_funnel (u v : Fin 10) (hne : u ≠ v) :
    ¬ ∃ a b : Bool, ∀ x : Fin 10 → Bool,
      target (Function.update (Function.update x u (!a)) v b) =
        target (Function.update (Function.update x u a) v (!b)) ∧
      target (Function.update (Function.update x u a) v (!b)) =
        target (Function.update (Function.update x u (!a)) v (!b)) := by
  rintro ⟨a, b, h⟩
  obtain ⟨x, hxv, hxu, hx0, hx1⟩ := restricted_sensitive v u hne.symm (!b)
  have hfalse : Function.update x u false = x := by
    rw [← hxu]
    exact Function.update_eq_self u x
  have hpin : ∀ c : Bool,
      Function.update (Function.update x u c) v (!b) = Function.update x u c := by
    intro c
    have hc : (Function.update x u c) v = !b := by
      simp [Function.update_of_ne hne.symm, hxv]
    rw [← hc, Function.update_eq_self]
  have he := (h x).2
  rw [hpin, hpin] at he
  cases a <;> simp only [Bool.not_false, Bool.not_true] at he <;>
    rw [hfalse, hx0, hx1] at he <;> cases he

def endpointPartner (v : Fin 10) : Fin 10 := if v = 0 then 2 else 0

def doublePinWitness (v u w : Fin 10) : Fin 10 → Bool :=
  Function.update (pinWitness u w true) (endpointPartner v) false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma endpoint_double_witness : ∀ (v u : Fin 10), (v = 0 ∨ v = 2) →
    u ≠ v → u ≠ endpointPartner v →
      ∃ w : Fin 10, w ≠ v ∧ w ≠ u ∧ w ≠ endpointPartner v ∧
        target (doublePinWitness v u w) = false ∧
        target (Function.update (doublePinWitness v u w) v true) = true := by
  decide

lemma endpoint_double_sensitive (v : Fin 10) (hv : v = 0 ∨ v = 2) (u : Fin 10)
    (huv : u ≠ v) (hup : u ≠ endpointPartner v) :
    ∃ x : Fin 10 → Bool, x (endpointPartner v) = false ∧ x u = true ∧
      x v = false ∧ target x = false ∧ target (Function.update x v true) = true := by
  obtain ⟨w, hwv, hwu, hwp, ht0, ht1⟩ := endpoint_double_witness v u hv huv hup
  have hvp : v ≠ endpointPartner v := by
    rcases hv with rfl | rfl <;> decide
  refine ⟨doublePinWitness v u w, ?_, ?_, ?_, ht0, ht1⟩
  · simp [doublePinWitness]
  · simp [doublePinWitness, pinWitness, Function.update_of_ne hup]
  · simp [doublePinWitness, pinWitness, Function.update_of_ne hvp,
      Function.update_of_ne huv.symm, hwv.symm]

end PEqualNP.Outside.L_meta_1890
