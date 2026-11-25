import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.MaximalFalse

lemma point_outside_other_line {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 1 ≤ q)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) : ∃ p, I p l ∧ ¬ I p m := by
  by_contra h
  have hsub : ∀ p, I p l → I p m := by simpa using h
  have hcard : 1 < (Finset.univ.filter fun p => I p l).card := by
    rw [hline]
    omega
  obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hcard
  have hpI : I p l := (Finset.mem_filter.mp hp).2
  have hp'I : I p' l := (Finset.mem_filter.mp hp').2
  obtain ⟨t, ht, huniq⟩ := hjoin p p' hne
  exact hlm ((huniq l ⟨hpI, hp'I⟩).trans
    (huniq m ⟨hsub p hpI, hsub p' hp'I⟩).symm)

def incidence {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (x y : Fin N → Bool) : Bool :=
  decide (∃ p l, I p l ∧ x p = true ∧ y l = true)

def raisedPoint {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (m : Fin N) (x : Fin N → Bool) : Fin N → Bool :=
  fun p => decide (¬ I p m) || x p

def raisedLine {N : ℕ} (m : Fin N) (y : Fin N → Bool) : Fin N → Bool :=
  fun l => decide (l = m) || y l

lemma above_line_baseline {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (houtside : ∀ l m : Fin N, l ≠ m → ∃ p, I p l ∧ ¬ I p m)
    (m : Fin N) (x y : Fin N → Bool) :
    incidence I (raisedPoint I m x) (raisedLine m y) =
      decide ((∃ p, I p m ∧ x p = true) ∨ (∃ l, l ≠ m ∧ y l = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [incidence, decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hI, hx, hy⟩
    by_cases hl : l = m
    · subst l
      exact Or.inl ⟨p, hI, by simpa [raisedPoint, hI] using hx⟩
    · exact Or.inr ⟨l, hl, by simpa [raisedLine, hl] using hy⟩
  · rintro (⟨p, hI, hx⟩ | ⟨l, hl, hy⟩)
    · exact ⟨p, m, hI, by simp [raisedPoint, hx], by simp [raisedLine]⟩
    · obtain ⟨p, hI, hnot⟩ := houtside l m hl
      exact ⟨p, l, hI, by simp [raisedPoint, hnot], by simp [raisedLine, hy]⟩

lemma plane_above_line_baseline {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (m : Fin N) (x y : Fin N → Bool) :
    incidence I (raisedPoint I m x) (raisedLine m y) =
      decide ((∃ p, I p m ∧ x p = true) ∨ (∃ l, l ≠ m ∧ y l = true)) := by
  exact above_line_baseline I
    (point_outside_other_line I (by omega) hline hjoin) m x y

lemma plane_baseline_zero_count {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (m : Fin N) :
    (Finset.univ.filter fun p => I p m).card +
      (Finset.univ.erase m).card = N + q := by
  rw [hline]
  have hN : 0 < N := Nat.zero_lt_of_lt m.isLt
  simp only [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ,
    Fintype.card_fin]
  omega

end PEqualNP.Outside.L_meta_2583_aux.MaximalFalse

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

namespace PEqualNP.Outside.L_meta_2583_aux.SensitivityBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2583_aux.MaximalFalse
open PEqualNP.Outside.L_meta_2583_aux.OrSensitivity

variable {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]

def edgeValue (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

def baseline (m : Fin N) : Fin (N + N) → Bool :=
  Fin.addCases (fun p => decide (¬ I p m)) (fun l => decide (l = m))

lemma point_ne_line (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  change p.val = N + l.val at this
  omega

lemma baseline_false (m : Fin N) : edgeValue I (baseline I m) = false := by
  simp [-Fin.natAdd_eq_addNat, edgeValue, baseline]

lemma point_sensitive (m p : Fin N) :
    Fin.castAdd N p ∈ sensitive (baseline I m) (edgeValue I) ↔ I p m := by
  simp only [sensitive, Finset.mem_filter, Finset.mem_univ, true_and, baseline_false,
    true_and]
  simp only [edgeValue, decide_eq_true_eq]
  constructor
  · rintro ⟨u, l, hul, hu, hl⟩
    have hl' : l = m := by
      simpa [-Fin.natAdd_eq_addNat, Function.update, baseline,
        Ne.symm (point_ne_line p l)] using hl
    subst l
    by_cases hup : u = p
    · simpa [hup] using hul
    · have hidx : Fin.castAdd N u ≠ Fin.castAdd N p := by
        intro h
        exact hup (Fin.castAdd_injective N N h)
      simp [Function.update, baseline, hidx, hul] at hu
  · intro hpm
    exact ⟨p, m, hpm, by simp, by simp [-Fin.natAdd_eq_addNat,
      Function.update, baseline, Ne.symm (point_ne_line p m)]⟩

lemma line_sensitive
    (houtside : ∀ l m : Fin N, l ≠ m → ∃ p, I p l ∧ ¬ I p m)
    (m l : Fin N) :
    Fin.natAdd N l ∈ sensitive (baseline I m) (edgeValue I) ↔ l ≠ m := by
  simp only [sensitive, Finset.mem_filter, Finset.mem_univ, true_and, baseline_false,
    true_and]
  constructor
  · intro h hlm
    subst l
    have eq : Function.update (baseline I m) (Fin.natAdd N m) true = baseline I m := by
      apply Function.update_eq_self_iff.mpr
      simp [-Fin.natAdd_eq_addNat, baseline]
    rw [eq, baseline_false] at h
    contradiction
  · intro hlm
    obtain ⟨p, hpl, hpm⟩ := houtside l m hlm
    rw [edgeValue, decide_eq_true_eq]
    exact ⟨p, l, hpl, by simp [-Fin.natAdd_eq_addNat,
      Function.update, baseline, point_ne_line p l, hpm], by simp⟩

lemma sensitivity_card (q : ℕ)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (houtside : ∀ l m : Fin N, l ≠ m → ∃ p, I p l ∧ ¬ I p m)
    (m : Fin N) :
    (sensitive (baseline I m) (edgeValue I)).card = N + q := by
  let A : Finset (Fin N) := Finset.univ.filter fun p => I p m
  let B : Finset (Fin N) := Finset.univ.erase m
  have disj : Disjoint (A.image (Fin.castAdd N)) (B.image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hb
    exact point_ne_line p l he.symm
  have eq : sensitive (baseline I m) (edgeValue I) =
      A.image (Fin.castAdd N) ∪ B.image (Fin.natAdd N) := by
    ext w
    refine Fin.addCases ?_ ?_ w
    · intro p
      rw [point_sensitive]
      constructor
      · intro hp
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, by simp [A, hp], rfl⟩)
      · intro hp
        rcases Finset.mem_union.mp hp with ha | hb
        · obtain ⟨p', hp', he⟩ := Finset.mem_image.mp ha
          have hh : p' = p := Fin.castAdd_injective N N he
          subst p'
          exact (Finset.mem_filter.mp hp').2
        · obtain ⟨l, _, he⟩ := Finset.mem_image.mp hb
          exact (point_ne_line p l he.symm).elim
    · intro l
      rw [line_sensitive I houtside]
      constructor
      · intro hl
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l, by simp [B, hl], rfl⟩)
      · intro hl
        rcases Finset.mem_union.mp hl with ha | hb
        · obtain ⟨p, _, he⟩ := Finset.mem_image.mp ha
          exact (point_ne_line p l he).elim
        · obtain ⟨l', hl', he⟩ := Finset.mem_image.mp hb
          have hh : l' = l := Fin.natAdd_injective N N he
          subst l'
          exact (Finset.mem_erase.mp hl').1
  rw [eq, Finset.card_union_of_disjoint disj,
    Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
    Finset.card_image_of_injective _ (Fin.natAdd_injective N N)]
  exact plane_baseline_zero_count I hline m

lemma plane_or_lower_bound {q : ℕ} (C : Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hao : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = edgeValue I z) :
    N + q - 1 ≤ orCount C.gates := by
  have hpos : 0 < N := by omega
  let m : Fin N := ⟨0, hpos⟩
  have bound := sensitivity_le_or_count C (baseline I m)
    (fun g hg => ⟨hao.1 g hg, hao.2.2 g hg⟩)
  have hc : circuitFun (N + N) C = edgeValue I := funext hC
  rw [hc, sensitivity_card I q hline
    (point_outside_other_line I (by omega) hline hjoin) m] at bound
  omega

end PEqualNP.Outside.L_meta_2583_aux.SensitivityBridge
