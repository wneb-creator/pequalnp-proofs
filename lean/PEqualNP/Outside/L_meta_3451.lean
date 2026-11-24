import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def decStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma decEvalMono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma decFoldMono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (gs.foldl decStep a).getD i false = true →
        (gs.foldl decStep b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [decStep, hl]
    · intro i hi
      unfold decStep at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact decEvalMono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma decWireMono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  refine decFoldMono C.gates (fun g hg => (hC g hg).1) _ _ (by simp) ?_ w
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin), List.getElem_ofFn] at hi ⊢
    exact hxy ⟨i, hin⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi

lemma decSingletonPoint (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (p : Fin N)
    (hp : ∃ l, ¬ I p l)
    (hpair : ∀ l, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false := by
  obtain ⟨l, hl⟩ := hp
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.castAdd N p))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inl (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair l hl] at hm
  cases hm

lemma decSingletonLine (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hC : Monotone2 C) (j : ℕ) (l : Fin N)
    (hl : ∃ p, ¬ I p l)
    (hpair : ∀ p, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    (C.wires (List.ofFn (fun k : Fin (N + N) =>
      decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  obtain ⟨p, hp⟩ := hl
  apply Bool.eq_false_iff.mpr
  intro ht
  have hm := decWireMono (N + N) C hC
    (fun k => decide (k = Fin.natAdd N l))
    (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l))
    (by intro k hk; exact decide_eq_true_iff.mpr (Or.inr (of_decide_eq_true hk)))
    (N + N + j) ht
  rw [hpair p hp] at hm
  cases hm

lemma decAndSingletons (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hD : Monotone2 D)
    (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hpair : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
      (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) :
    ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false := by
  intro j hj ha
  constructor
  · intro p
    exact decSingletonPoint N I D hD j p (hp p) (hpair j hj ha p)
  · intro l
    exact decSingletonLine N I D hD j l (hl l) (fun p h => hpair j hj ha p l h)

lemma decFinish (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hp : ∀ p, ∃ l, ¬ I p l) (hl : ∀ l, ∃ p, ¬ I p l)
    (hclean : ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  obtain ⟨D, hm, hr, hs, hf, hpair⟩ := hclean
  exact ⟨D, hm, hr, hs, hf, hpair, decAndSingletons N I D hm hp hl hpair⟩

lemma decUniversalPointDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p : Fin N) (hp : ∀ l, I p l) (q : Fin N) (hq : q ≠ p)
    (l l' : Fin N) (hl : I q l) (hl' : I q l') : l = l' := by
  by_contra hne
  exact hfour p q l l' (Ne.symm hq) hne ⟨hp l, hp l', hl, hl'⟩

lemma decUniversalLineDegree (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l : Fin N) (hl : ∀ p, I p l) (k : Fin N) (hk : k ≠ l)
    (p p' : Fin N) (hp : I p k) (hp' : I p' k) : p = p' := by
  by_contra hne
  exact hfour p p' l k hne (Ne.symm hk) ⟨hl p, hp, hl p', hp'⟩

lemma edgeless (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  refine ⟨⟨[], N + N⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro z
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD_eq_getElem?_getD, hI]
  · simp
  · simp

lemma positive_size (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∃ p l, I p l)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    0 < C.size := by
  by_contra! hsize
  have hnil : C.gates = [] := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using Nat.eq_zero_of_le_zero hsize
  obtain ⟨p, l, hpl⟩ := hI
  have hall : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => true) = true :=
    (hfun _).mpr ⟨p, l, hpl, rfl, rfl⟩
  have hout : C.output < N + N := by
    by_contra! hbound
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.foldl_nil] at hall
    rw [List.getD_eq_default _ _ (by simpa using hbound)] at hall
    cases hall
  let i : Fin (N + N) := ⟨C.output, hout⟩
  let z : Fin (N + N) → Bool := fun k => decide (k = i)
  have hz : PEqualNP.MetaComplexity.circuitFun (N + N) C z = true := by
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.getD_eq_getElem?_getD, hout, z, i]
  obtain ⟨p', l', _, hp', hl'⟩ := (hfun z).mp hz
  simp only [z, decide_eq_true_eq] at hp' hl'
  have heq := congrArg Fin.val (hp'.trans hl'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  have hpbound := p'.isLt
  omega

lemma one_point (I : Fin 1 → Fin 1 → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (1 + 1) → Bool,
      PEqualNP.MetaComplexity.circuitFun (1 + 1) C z = true ↔
      ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + 1) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (1 + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (1 + 1) D z = true ↔ ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin 1, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (1 + 1) => decide (ke = Fin.castAdd 1 p0 ∨ ke = Fin.natAdd 1 l0)))).getD (1 + 1 + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin 1, (D.wires (List.ofFn (fun kc : Fin (1 + 1) => decide (kc = Fin.castAdd 1 p)))).getD (1 + 1 + j) false = false) ∧ ∀ l : Fin 1, (D.wires (List.ofFn (fun kd : Fin (1 + 1) => decide (kd = Fin.natAdd 1 l)))).getD (1 + 1 + j) false = false) := by
  by_cases hI : I 0 0
  · let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    have hIall (p l : Fin 1) : I p l := by
      have hp : p = 0 := Subsingleton.elim _ _
      have hl : l = 0 := Subsingleton.elim _ _
      simpa [hp, hl] using hI
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2, D]
    · decide
    · have hsize := positive_size 1 I C ⟨0, 0, hI⟩ hfun
      change 1 ≤ C.size
      omega
    · intro z
      simp [D, PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.ofFn_succ, Fin.exists_fin_one, hIall]
    · intro j hj hop p l hn
      exact (hn (hIall p l)).elim
    · intro j hj _
      have hj0 : j = 0 := by simpa [D] using hj
      subst j
      constructor <;> intro p <;> fin_cases p <;> decide
  · apply edgeless 1 I C
    intro p l
    have hp : p = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    simpa [hp, hl] using hI

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def zResWire {m n : ℕ} (r : Fin m → Option (Fin n)) (i : ℕ) : Option ℕ :=
  if hi : i < m then (r ⟨i, hi⟩).map Fin.val else some (n + (i - m))

def zResGate (ρ : ℕ → Option ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.any (fun i => (ρ i).isNone) then ⟨.or, []⟩
      else ⟨.and, g.inputs.filterMap ρ⟩
  | op => ⟨op, g.inputs.filterMap ρ⟩

def zResCircuit {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (zResGate (zResWire r)), (zResWire r C.output).getD (n + C.size)⟩

def zResInput {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) : Fin m → Bool :=
  fun i => (r i).elim false z

lemma zRes_size {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) :
    (zResCircuit r C).size = C.size := by
  simp [zResCircuit, Circuit.size]

lemma zRes_gate_mono (ρ : ℕ → Option ℕ) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ((zResGate ρ g).op = .and ∨ (zResGate ρ g).op = .or) ∧
      (zResGate ρ g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  · simp only [zResGate]
    split
    · simp
    · exact ⟨Or.inl rfl, (List.length_filterMap_le ρ ins).trans hlen⟩
  · exact ⟨Or.inr rfl, (List.length_filterMap_le ρ ins).trans hlen⟩

lemma zRes_monotone {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (zResCircuit r C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  exact zRes_gate_mono _ _ (hC g₀ hg₀).1 (hC g₀ hg₀).2

lemma zRes_gate_eval (ρ : ℕ → Option ℕ) (g : Gate) (a b : ℕ → Bool)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2)
    (hval : ∀ i, (ρ i).elim false b = a i) :
    (zResGate ρ g).op.eval ((zResGate ρ g).inputs.map b) =
      g.op.eval (g.inputs.map a) := by
  rcases g with ⟨op, ins⟩
  rcases hop with rfl | rfl
  all_goals
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, ins⟩⟩⟩
    · simp [zResGate, GateOp.eval]
    · specialize hval i
      cases hρ : ρ i <;> simp_all [zResGate, GateOp.eval]
    · have hi := hval i
      have hj := hval j
      cases hρi : ρ i <;> cases hρj : ρ j <;> simp_all [zResGate, GateOp.eval]
    · simp at hlen

lemma zRes_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = w.length
    · subst i; simp
    · rw [if_neg he, List.getD_eq_default w false (by omega),
        List.getD_eq_default [v] false (by simp; omega)]

lemma zRes_wire_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (j : ℕ) :
    zResWire r (m + j) = some (n + j) := by
  simp [zResWire]

lemma zRes_step_rel {m n : ℕ} (r : Fin m → Option (Fin n))
    (a b : List Bool) (k : ℕ) (ha : a.length = m + k) (hb : b.length = n + k)
    (hv : ∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false)
    (v : Bool) :
    ∀ i, (zResWire r i).elim false (fun j => (b ++ [v]).getD j false) =
      (a ++ [v]).getD i false := by
  intro i
  have hv_i := hv i
  rw [zRes_snoc, ha]
  by_cases hi : i < m
  · have he : i ≠ m + k := by omega
    rw [if_neg he]
    rw [zResWire, dif_pos hi] at hv_i ⊢
    cases hri : r ⟨i, hi⟩ with
    | none => simpa [hri] using hv_i
    | some j =>
      have hj : j.val < b.length := by rw [hb]; omega
      simp only [hri, Option.map_some, Option.elim_some] at hv_i ⊢
      rw [List.getD_append _ _ _ _ hj]
      exact hv_i
  · rw [zResWire, dif_neg hi] at hv_i ⊢
    simp only [Option.elim_some]
    rw [zRes_snoc, hb]
    by_cases he : i = m + k
    · subst i; simp
    · have he' : n + (i - m) ≠ n + k := by omega
      rw [if_neg he, if_neg he']
      simpa [zResWire, hi] using hv_i

lemma zRes_fold_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (gs : List Gate) :
    ∀ (a b : List Bool) (k : ℕ), a.length = m + k → b.length = n + k →
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
      (∀ i, (zResWire r i).elim false (fun j => b.getD j false) = a.getD i false) →
      ∀ i, (zResWire r i).elim false (fun j =>
        ((gs.map (zResGate (zResWire r))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) b).getD j false) =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]) a).getD i false := by
  induction gs with
  | nil => intro a b k ha hb hgs hv i; exact hv i
  | cons g gs ih =>
    intro a b k ha hb hgs hv
    have hg := hgs g (by simp)
    have he := zRes_gate_eval (zResWire r) g (fun i => a.getD i false)
      (fun i => b.getD i false) hg.1 hg.2 hv
    simp only [List.map_cons, List.foldl_cons, he]
    apply ih _ _ (k + 1)
    · simp [ha]; omega
    · simp [hb]; omega
    · intro g' hg'; exact hgs g' (by simp [hg'])
    · exact zRes_step_rel r a b k ha hb hv _

lemma zRes_input_rel {m n : ℕ} (r : Fin m → Option (Fin n)) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => (List.ofFn z).getD j false) =
      (List.ofFn (zResInput r z)).getD i false := by
  by_cases hi : i < m
  · simp only [zResWire, dif_pos hi]
    rw [List.getD_eq_getElem _ _ (by simp [hi])]
    simp only [List.getElem_ofFn, zResInput]
    cases hr : r ⟨i, hi⟩ with
    | none => rfl
    | some j => simp [j.isLt]
  · simp [zResWire, hi, List.getD_eq_default, zResInput]

lemma zRes_wires {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (i : ℕ) :
    (zResWire r i).elim false (fun j => ((zResCircuit r C).wires (List.ofFn z)).getD j false) =
      (C.wires (List.ofFn (zResInput r z))).getD i false := by
  exact zRes_fold_rel r C.gates _ _ 0 (by simp) (by simp) hC
    (zRes_input_rel r z) i

lemma zRes_wires_gate {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) (j : ℕ) :
    ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
      (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  simpa [zRes_wire_gate] using zRes_wires r C hC z (m + j)

lemma zRes_gateAt {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit) (j : ℕ) :
    gateAt (zResCircuit r C) j = zResGate (zResWire r) (gateAt C j) := by
  have he : zResGate (zResWire r) ⟨.or, []⟩ = ⟨.or, []⟩ := rfl
  unfold gateAt zResCircuit
  change (C.gates.map (zResGate (zResWire r))).getD j _ = _
  simpa only [he] using List.getD_map (n := j) C.gates ⟨GateOp.or, []⟩
    (zResGate (zResWire r))

lemma zRes_inputs (ρ : ℕ → Option ℕ) (g : Gate) (i : ℕ)
    (hi : i ∈ (zResGate ρ g).inputs) : ∃ j ∈ g.inputs, ρ j = some i := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [zResGate] at hi
    · split at hi
      · simp at hi
      · exact List.mem_filterMap.mp hi
    all_goals exact List.mem_filterMap.mp hi

lemma zRes_wire_lt {m n : ℕ} (r : Fin m → Option (Fin n)) (i j k : ℕ)
    (hi : i < m + k) (hr : zResWire r i = some j) : j < n + k := by
  by_cases him : i < m
  · simp only [zResWire, dif_pos him] at hr
    cases he : r ⟨i, him⟩ with
    | none => simp [he] at hr
    | some t => simp [he] at hr; subst j; omega
  · simp only [zResWire, dif_neg him, Option.some.injEq] at hr
    omega

lemma zRes_readsBack {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : ReadsBack m C) : ReadsBack n (zResCircuit r C) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [zResCircuit] using hj
  rw [zRes_gateAt] at hi
  obtain ⟨k, hk, hki⟩ := zRes_inputs _ _ _ hi
  exact zRes_wire_lt r k i j (hC j hj' k hk) hki

lemma zRes_and_source (ρ : ℕ → Option ℕ) (g : Gate)
    (h : (zResGate ρ g).op = .and) : g.op = .and := by
  cases g with
  | mk op ins =>
    cases op <;> simp_all [zResGate]

lemma zRes_and_wire {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (j : ℕ) (hj : (gateAt (zResCircuit r C) j).op = .and)
    (z : Fin n → Bool) :
    (gateAt C j).op = .and ∧
      ((zResCircuit r C).wires (List.ofFn z)).getD (n + j) false =
        (C.wires (List.ofFn (zResInput r z))).getD (m + j) false := by
  rw [zRes_gateAt] at hj
  exact ⟨zRes_and_source _ _ hj, zRes_wires_gate r C hC z j⟩

lemma zRes_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  have hf : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp; omega
  exact hf C.gates x

lemma zRes_eval {m n : ℕ} (r : Fin m → Option (Fin n)) (C : Circuit)
    (hC : Monotone2 C) (z : Fin n → Bool) :
    circuitFun n (zResCircuit r C) z = circuitFun m C (zResInput r z) := by
  have hv := zRes_wires r C hC z C.output
  change ((zResCircuit r C).wires (List.ofFn z)).getD
      ((zResWire r C.output).getD (n + C.size)) false = _
  cases hr : zResWire r C.output with
  | none =>
    simp only [hr, Option.elim_none] at hv
    rw [Option.getD_none, List.getD_eq_default _ false (by
      rw [zRes_wires_length]
      simp [zResCircuit, Circuit.size])]
    exact hv
  | some j => simpa [hr, circuitFun, Circuit.eval] using hv

lemma decMinCover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n),
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
      ∀ T' : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T' ∨ j ∈ T') → T.card ≤ T'.card := by
  classical
  let P : ℕ → Prop := fun k => ∃ T : Finset (Fin n),
    (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ T.card = k
  have hex : ∃ k, P k := ⟨n, Finset.univ, by simp, by simp⟩
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hT, ?_⟩
  intro T' hT'
  rw [hcard]
  exact Nat.find_min' hex ⟨T', hT', rfl⟩

def padI {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin (N + 1)) : Prop :=
  ∃ a b : Fin N, p = a.castSucc ∧ l = b.castSucc ∧ I a b

def padLift {N : ℕ} : Fin (N + N) → Option (Fin ((N + 1) + (N + 1))) :=
  Fin.addCases (fun p => some (Fin.castAdd (N + 1) p.castSucc))
    (fun l => some (Fin.natAdd (N + 1) l.castSucc))

def padDrop {N : ℕ} : Fin ((N + 1) + (N + 1)) → Option (Fin (N + N)) :=
  Fin.addCases (Fin.lastCases none (fun p => some (Fin.castAdd N p)))
    (Fin.lastCases none (fun l => some (Fin.natAdd N l)))

lemma padI_cast {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    padI I p.castSucc l.castSucc ↔ I p l := by
  simp [padI]

lemma padI_point_last {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin (N + 1)) :
    ¬ padI I (Fin.last N) l := by
  rintro ⟨a, b, h, _, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_line_last {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin (N + 1)) :
    ¬ padI I p (Fin.last N) := by
  rintro ⟨a, b, _, h, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_noRect {N : ℕ} (I : Fin N → Fin N → Prop)
    (h : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ p p' l l' : Fin (N + 1), p ≠ p' → l ≠ l' →
      ¬ (padI I p l ∧ padI I p l' ∧ padI I p' l ∧ padI I p' l') := by
  rintro p p' l l' hpp hll ⟨⟨a, b, rfl, rfl, hab⟩, h1, h2, h3⟩
  obtain ⟨a', d, ha', rfl, had⟩ := h1
  have haa : a = a' := Fin.castSucc_injective N ha'
  subst a'
  obtain ⟨c, b', rfl, hb', hcb⟩ := h2
  have hbb : b = b' := Fin.castSucc_injective N hb'
  subst b'
  have hcd := (padI_cast I c d).mp h3
  exact h a c b d (fun e => hpp (congrArg Fin.castSucc e))
    (fun e => hll (congrArg Fin.castSucc e)) ⟨hab, had, hcb, hcd⟩

lemma padLift_input_point {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (p : Fin N) :
    zResInput padLift z (Fin.castAdd N p) = z (Fin.castAdd (N + 1) p.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padLift_input_line {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (l : Fin N) :
    zResInput padLift z (Fin.natAdd N l) = z (Fin.natAdd (N + 1) l.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padDrop_input_point {N : ℕ} (z : Fin (N + N) → Bool) (p : Fin N) :
    zResInput padDrop z (Fin.castAdd (N + 1) p.castSucc) = z (Fin.castAdd N p) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padDrop_input_line {N : ℕ} (z : Fin (N + N) → Bool) (l : Fin N) :
    zResInput padDrop z (Fin.natAdd (N + 1) l.castSucc) = z (Fin.natAdd N l) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padLift_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) (zResCircuit (padLift (N := N)) C) z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨p.castSucc, l.castSucc, (padI_cast I p l).mpr hpl,
      by simpa only [padLift_input_point] using hp, by simpa only [padLift_input_line] using hl⟩
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padLift_input_point] using hp,
      by simpa only [padLift_input_line] using hl⟩

lemma padDrop_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) C z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) (zResCircuit (padDrop (N := N)) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padDrop_input_point] using hp,
      by simpa only [padDrop_input_line] using hl⟩
  · rintro ⟨a, b, hab, hp, hl⟩
    exact ⟨a.castSucc, b.castSucc, (padI_cast I a b).mpr hab,
      by simpa only [padDrop_input_point] using hp, by simpa only [padDrop_input_line] using hl⟩

lemma padDrop_pair {N : ℕ} (p l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) =>
        decide (k = Fin.castAdd (N + 1) p.castSucc ∨ k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_point {N : ℕ} (p : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.castAdd (N + 1) p.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_line {N : ℕ} (l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padSuffices (hclean : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C hfour hC hrC hfC
  classical
  let C' := zResCircuit (padLift (N := N)) C
  have hC' : Monotone2 C' := zRes_monotone _ _ hC
  have hrC' : ReadsBack ((N + 1) + (N + 1)) C' := zRes_readsBack _ _ hrC
  have hfC' := padLift_computes I C hC hfC
  obtain ⟨D, hD, hrD, hsD, hfD, hpD⟩ :=
    hclean (N + 1) (padI I) C' (padI_noRect I hfour) hC' hrC' hfC'
  have hsingle := decAndSingletons (N + 1) (padI I) D hD
    (fun p => ⟨Fin.last N, padI_line_last I p⟩)
    (fun l => ⟨Fin.last N, padI_point_last I l⟩) hpD
  let E := zResCircuit (padDrop (N := N)) D
  refine ⟨E, zRes_monotone _ _ hD, zRes_readsBack _ _ hrD, ?_,
    padDrop_computes I D hD hfD, ?_, ?_⟩
  · simpa only [E, C', zRes_size] using hsD
  · intro j hj hand p l hpl
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
    rw [zRes_wires_gate _ _ hD, padDrop_pair]
    exact hpD j hj' hand' p.castSucc l.castSucc (fun h => hpl ((padI_cast I p l).mp h))
  · intro j hj hand
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    constructor
    · intro p
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_point]
      exact (hsingle j hj' hand').1 p.castSucc
    · intro l
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_line]
      exact (hsingle j hj' hand').2 l.castSucc

end PEqualNP.Outside.L_meta_3451
