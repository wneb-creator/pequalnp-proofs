import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.OrSensitivity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sensitive {n : ℕ} (a : Fin n → Bool) (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => f a = false ∧ f (Function.update a i true) = true

lemma sensitive_false {n : ℕ} (a : Fin n → Bool) :
    sensitive a (fun _ => false) = ∅ := by simp [sensitive]

lemma sensitive_input {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    sensitive a (fun x => x i) ⊆ {i} := by
  intro j hj
  obtain ⟨hfalse, htrue⟩ := (Finset.mem_filter.mp hj).2
  by_cases hji : j = i
  · simp [hji]
  · change Function.update a j true i = true at htrue
    rw [Function.update_of_ne (Ne.symm hji)] at htrue
    simp_all

lemma sensitive_or {n : ℕ} (a : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) :
    sensitive a (fun x => f x || g x) ⊆ sensitive a f ∪ sensitive a g := by
  intro i hi
  obtain ⟨hf, ht⟩ := (Finset.mem_filter.mp hi).2
  have hf' : f a = false ∧ g a = false := by
    cases h1 : f a <;> cases h2 : g a <;> simp_all
  simp only [Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'.1, ht⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'.2, ht⟩)

lemma sensitive_and {n : ℕ} (a : Fin n → Bool)
    (f g : (Fin n → Bool) → Bool) :
    sensitive a (fun x => f x && g x) ⊆ sensitive a f ∨
      sensitive a (fun x => f x && g x) ⊆ sensitive a g := by
  by_cases hf : f a = false
  · left
    intro i hi
    have ht := (Finset.mem_filter.mp hi).2.2
    simp only [Bool.and_eq_true] at ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, ht.1⟩
  · right
    intro i hi
    obtain ⟨hb, ht⟩ := (Finset.mem_filter.mp hi).2
    have hg : g a = false := by
      cases h1 : f a <;> cases h2 : g a <;> simp_all
    simp only [Bool.and_eq_true] at ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg, ht.2⟩

def gateFunction {n : ℕ} (F : List ((Fin n → Bool) → Bool)) (g : Gate) :
    (Fin n → Bool) → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => (F.getD i (fun _ => false)) x)

def orWeight (g : Gate) : ℕ := match g.op with | .or => 1 | _ => 0

def orCount (gs : List Gate) : ℕ := (gs.map orWeight).sum

lemma gate_sensitive {n : ℕ} (a : Fin n → Bool)
    (F : List ((Fin n → Bool) → Bool)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    ∃ J : Finset ℕ, J.card ≤ 1 + orWeight g ∧
      sensitive a (gateFunction F g) ⊆
        J.biUnion fun j => sensitive a (F.getD j (fun _ => false)) := by
  obtain ⟨u, v, hins⟩ : ∃ u v, g.inputs = [u, v] := by
    cases hi : g.inputs with
    | nil => simp [hi] at hlen
    | cons u rest =>
      cases hr : rest with
      | nil => simp [hi, hr] at hlen
      | cons v tail =>
        have ht : tail = [] := by simpa [hi, hr] using hlen
        exact ⟨u, v, by simp [ht]⟩
  rcases hop with hop | hop
  · have heq : gateFunction F g =
        (fun x => (F.getD u (fun _ => false)) x && (F.getD v (fun _ => false)) x) := by
      funext x
      simp [gateFunction, hop, hins, GateOp.eval]
    have hs := sensitive_and a (F.getD u (fun _ => false))
      (F.getD v (fun _ => false))
    rcases hs with hs | hs
    · refine ⟨{u}, by simp [orWeight, hop], ?_⟩
      rw [heq]
      simpa using hs
    · refine ⟨{v}, by simp [orWeight, hop], ?_⟩
      rw [heq]
      simpa using hs
  · have heq : gateFunction F g =
        (fun x => (F.getD u (fun _ => false)) x || (F.getD v (fun _ => false)) x) := by
      funext x
      simp [gateFunction, hop, hins, GateOp.eval]
    refine ⟨{u, v}, ?_, ?_⟩
    · have := Finset.card_insert_le u ({v} : Finset ℕ)
      simpa [orWeight, hop] using this
    · rw [heq]
      simpa using
        sensitive_or a (F.getD u (fun _ => false)) (F.getD v (fun _ => false))

def Count {n : ℕ} (a : Fin n → Bool) (t : ℕ)
    (F : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ W : Finset ℕ,
    (W.biUnion fun j => sensitive a (F.getD j (fun _ => false))).card ≤ t + W.card

lemma getD_snoc_ne {α : Type*} (L : List α) (s d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [s]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma count_step {n : ℕ} (a : Fin n → Bool) (t : ℕ)
    (F : List ((Fin n → Bool) → Bool)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2)
    (hc : Count a t F) : Count a (t + orWeight g) (F ++ [gateFunction F g]) := by
  obtain ⟨J, hJ, hs⟩ := gate_sensitive a F g hop hlen
  intro W
  by_cases hW : F.length ∈ W
  · have hsub :
        (W.biUnion fun j => sensitive a ((F ++ [gateFunction F g]).getD j (fun _ => false))) ⊆
        ((W.erase F.length ∪ J).biUnion fun j => sensitive a (F.getD j (fun _ => false))) := by
      intro i hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      by_cases he : j = F.length
      · subst j
        have heq : (F ++ [gateFunction F g]).getD F.length (fun _ => false) =
            gateFunction F g := by simp
        rw [heq] at hij
        obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp (hs hij)
        exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_union_right _ hk, hik⟩
      · rw [getD_snoc_ne _ _ _ _ he] at hij
        exact Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hj⟩), hij⟩
    have hcard : (W.erase F.length ∪ J).card ≤ W.card - 1 + (1 + orWeight g) := by
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left hJ _
    have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hW⟩
    have h1 := Finset.card_le_card hsub
    have h2 := hc (W.erase F.length ∪ J)
    omega
  · have heq :
        (W.biUnion fun j => sensitive a ((F ++ [gateFunction F g]).getD j (fun _ => false))) =
        (W.biUnion fun j => sensitive a (F.getD j (fun _ => false))) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      rw [getD_snoc_ne _ _ _ _ (fun he => hW (he ▸ hj))]
    rw [heq]
    exact (hc W).trans (by omega)

def inputFunctions (n : ℕ) : List ((Fin n → Bool) → Bool) :=
  List.ofFn fun i : Fin n => fun x => x i

lemma count_inputs {n : ℕ} (a : Fin n → Bool) : Count a 0 (inputFunctions n) := by
  intro W
  refine Finset.card_biUnion_le.trans ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < n
  · have heq : (inputFunctions n).getD j (fun _ => false) =
        (fun x => x ⟨j, hj⟩) := by simp [inputFunctions, hj]
    rw [heq]
    exact (Finset.card_le_card (sensitive_input a ⟨j, hj⟩)).trans (by simp)
  · rw [List.getD_eq_default _ _ (by simp [inputFunctions]; omega), sensitive_false]
    simp

def runFunctions {n : ℕ} : List Gate → List ((Fin n → Bool) → Bool) →
    List ((Fin n → Bool) → Bool)
  | [], F => F
  | g :: gs, F => runFunctions gs (F ++ [gateFunction F g])

lemma count_run {n : ℕ} (a : Fin n → Bool) (gs : List Gate) (t : ℕ)
    (F : List ((Fin n → Bool) → Bool))
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (hc : Count a t F) : Count a (t + orCount gs) (runFunctions gs F) := by
  induction gs generalizing t F with
  | nil => simpa [runFunctions, orCount] using hc
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    have hr := ih (t + orWeight g) (F ++ [gateFunction F g])
      (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      (count_step a t F g hg.1 hg.2 hc)
    simpa [runFunctions, orCount, Nat.add_assoc] using hr

lemma map_eval_getD {n : ℕ} (F : List ((Fin n → Bool) → Bool))
    (x : Fin n → Bool) (i : ℕ) :
    (F.map fun f => f x).getD i false = (F.getD i (fun _ => false)) x := by
  induction F generalizing i with
  | nil => simp
  | cons f F ih => cases i <;> simp_all

lemma runFunctions_eval {n : ℕ} (gs : List Gate)
    (F : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (runFunctions gs F).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (F.map fun f => f x) := by
  induction gs generalizing F with
  | nil => rfl
  | cons g gs ih =>
    rw [runFunctions, ih, List.foldl_cons]
    congr 1
    simp only [List.map_append, List.map_singleton, gateFunction]
    congr 2
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i _
    exact (map_eval_getD F x i).symm

lemma output_function {n : ℕ} (C : Circuit) :
    (runFunctions C.gates (inputFunctions n)).getD C.output (fun _ => false) =
      circuitFun n C := by
  funext x
  rw [← map_eval_getD, runFunctions_eval]
  simp [inputFunctions, circuitFun, Circuit.eval, Circuit.wires, Function.comp_def]

lemma sensitivity_le_or_count {n : ℕ} (C : Circuit) (a : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (sensitive a (circuitFun n C)).card ≤ orCount C.gates + 1 := by
  have hc := count_run a C.gates 0 (inputFunctions n) hC (count_inputs a)
  have h := hc {C.output}
  have h' : (sensitive a
      ((runFunctions C.gates (inputFunctions n)).getD C.output (fun _ => false))).card ≤
      orCount C.gates + 1 := by simpa using h
  rw [output_function] at h'
  exact h'

end PEqualNP.Outside.L_meta_2583_aux.OrSensitivity
