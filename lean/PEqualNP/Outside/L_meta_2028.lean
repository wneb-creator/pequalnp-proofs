import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028

lemma size_pos_of_nonempty_edge_function (n : ℕ) (G : SimpleGraph (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    0 < C.size := by
  classical
  by_contra hpos
  have hsize : C.size = 0 := Nat.eq_zero_of_not_pos hpos
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hsize
  by_cases hout : C.output < n
  · let i : Fin n := ⟨C.output, hout⟩
    let x : Fin n → Bool := fun j => decide (j = i)
    have heval : C.eval (List.ofFn x) = true := by
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, hnil,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hout, x, i]
    obtain ⟨u, v, huv, hu, hv⟩ := (hcomp x).mp heval
    have hui : u = i := by simpa [x] using hu
    have hvi : v = i := by simpa [x] using hv
    subst u
    subst v
    exact G.loopless.irrefl _ huv
  · have heval : C.eval (List.ofFn fun _ : Fin n => true) = true := by
      apply (hcomp _).mpr
      obtain ⟨u, v, huv⟩ := hedge
      exact ⟨u, v, huv, rfl, rfl⟩
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hout] at heval

namespace AndGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def JoinLists (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
    ∀ i, c.getD i false = (a.getD i false || b.getD i false)

lemma joinLists_append {a b c : List Bool} (h : JoinLists a b c)
    (u v w : Bool) (hw : w = (u || v)) :
    JoinLists (a ++ [u]) (b ++ [v]) (c ++ [w]) := by
  obtain ⟨hab, hac, h⟩ := h
  refine ⟨by simp [hab], by simp [hac], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append c [w] false i (by omega),
      List.getD_append a [u] false i hi,
      List.getD_append b [v] false i (by omega)]
    exact h i
  · rw [List.getD_append_right c [w] false i (by omega),
      List.getD_append_right a [u] false i (by omega),
      List.getD_append_right b [v] false i (by omega), ← hac, ← hab]
    cases hd : i - a.length with
    | zero => simpa using hw
    | succ k => simp

lemma any_join (is : List ℕ) (f g : ℕ → Bool) :
    is.any (fun i => f i || g i) = (is.any f || is.any g) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.any_cons, ih]
    cases f i <;> cases g i <;> simp

lemma or_gate_join {a b c : List Bool} (h : JoinLists a b c) (g : Gate)
    (hop : g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) ||
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq]
  calc
    g.inputs.any (fun i => c.getD i false) =
        g.inputs.any (fun i => a.getD i false || b.getD i false) := by
      congr 1
      funext i
      exact h.2.2 i
    _ = _ := any_join _ _ _

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_join (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.or)
    (a b c : List Bool) (h : JoinLists a b c) :
    JoinLists (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact joinLists_append h _ _ _ (or_gate_join h g (hgs g (by simp)))

lemma or_only_eval_join (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or) (x y : Fin n → Bool) :
    C.eval (List.ofFn fun i => x i || y i) =
      (C.eval (List.ofFn x) || C.eval (List.ofFn y)) := by
  have hin : JoinLists (List.ofFn x) (List.ofFn y)
      (List.ofFn fun i => x i || y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;>
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
  exact (fold_join C.gates hC _ _ _ hin).2.2 C.output

lemma has_and_of_nonempty_edge_function (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (hedge : ∃ u v : Fin n, G.Adj u v) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ g ∈ C.gates, g.op = GateOp.and := by
  classical
  by_contra hnot
  have hor : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    have hop := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · exact False.elim (hnot ⟨g, hg, ha⟩)
    · exact ho
  have hsingle (i : Fin n) :
      C.eval (List.ofFn fun j : Fin n => decide (j = i)) = false := by
    cases heval : C.eval (List.ofFn fun j : Fin n => decide (j = i)) with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := (hcomp _).mp heval
      have hui : u = i := by simpa using hu
      have hvi : v = i := by simpa using hv
      subst u
      subst v
      exact False.elim (G.loopless.irrefl _ huv)
  obtain ⟨u, v, huv⟩ := hedge
  have hpair : C.eval (List.ofFn fun i : Fin n => decide (i = u) || decide (i = v)) = true := by
    apply (hcomp _).mpr
    exact ⟨u, v, huv, by simp, by simp⟩
  rw [or_only_eval_join n C hor, hsingle u, hsingle v] at hpair
  cases hpair

end AndGate

namespace OrGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def MeetLists (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
    ∀ i, c.getD i false = (a.getD i false && b.getD i false)

lemma meetLists_append {a b c : List Bool} (h : MeetLists a b c)
    (u v w : Bool) (hw : w = (u && v)) :
    MeetLists (a ++ [u]) (b ++ [v]) (c ++ [w]) := by
  obtain ⟨hab, hac, h⟩ := h
  refine ⟨by simp [hab], by simp [hac], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append c [w] false i (by omega),
      List.getD_append a [u] false i hi,
      List.getD_append b [v] false i (by omega)]
    exact h i
  · rw [List.getD_append_right c [w] false i (by omega),
      List.getD_append_right a [u] false i (by omega),
      List.getD_append_right b [v] false i (by omega), ← hac, ← hab]
    cases hd : i - a.length with
    | zero => simpa using hw
    | succ k => simp

lemma all_meet (is : List ℕ) (f g : ℕ → Bool) :
    is.all (fun i => f i && g i) = (is.all f && is.all g) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, ih]
    cases f i <;> cases g i <;> simp

lemma and_gate_meet {a b c : List Bool} (h : MeetLists a b c) (g : Gate)
    (hop : g.op = GateOp.and) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) &&
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq]
  calc
    g.inputs.all (fun i => c.getD i false) =
        g.inputs.all (fun i => a.getD i false && b.getD i false) := by
      congr 1
      funext i
      exact h.2.2 i
    _ = _ := all_meet _ _ _

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_meet (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and)
    (a b c : List Bool) (h : MeetLists a b c) :
    MeetLists (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact meetLists_append h _ _ _ (and_gate_meet h g (hgs g (by simp)))

lemma and_only_eval_meet (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and) (x y : Fin n → Bool) :
    C.eval (List.ofFn fun i => x i && y i) =
      (C.eval (List.ofFn x) && C.eval (List.ofFn y)) := by
  have hin : MeetLists (List.ofFn x) (List.ofFn y)
      (List.ofFn fun i => x i && y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  exact (fold_meet C.gates hC _ _ _ hin).2.2 C.output

lemma pair_eq_of_mem {n : ℕ} (u v a b : Fin n) (hne : u ≠ v)
    (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) : s(u, v) = s(a, b) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · contradiction
  · rfl
  · exact Sym2.eq_swap
  · contradiction

lemma has_or_of_distinct_edges (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ g ∈ C.gates, g.op = GateOp.or := by
  classical
  by_contra hnot
  have hand : ∀ g ∈ C.gates, g.op = GateOp.and := by
    intro g hg
    have hop := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · exact ha
    · exact False.elim (hnot ⟨g, hg, ho⟩)
  let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
  let y : Fin n → Bool := fun i => decide (i = c ∨ i = d)
  have hx : C.eval (List.ofFn x) = true :=
    (hcomp x).mpr ⟨a, b, hab, by simp [x], by simp [x]⟩
  have hy : C.eval (List.ofFn y) = true :=
    (hcomp y).mpr ⟨c, d, hcd, by simp [y], by simp [y]⟩
  have hxy : C.eval (List.ofFn fun i => x i && y i) = true := by
    rw [and_only_eval_meet n C hand, hx, hy]
    rfl
  obtain ⟨u, v, huv, hu, hv⟩ := (hcomp _).mp hxy
  have huvne : u ≠ v := by
    intro heq
    subst v
    exact G.loopless.irrefl _ huv
  have hu' : (u = a ∨ u = b) ∧ (u = c ∨ u = d) := by simpa [x, y] using hu
  have hv' : (v = a ∨ v = b) ∧ (v = c ∨ v = d) := by simpa [x, y] using hv
  exact hne ((pair_eq_of_mem u v a b huvne hu'.1 hv'.1).symm.trans
    (pair_eq_of_mem u v c d huvne hu'.2 hv'.2))

end OrGate


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma size_ge_two_of_and_or (C : Circuit)
    (hand : ∃ g ∈ C.gates, g.op = GateOp.and)
    (hor : ∃ g ∈ C.gates, g.op = GateOp.or) : 2 ≤ C.size := by
  obtain ⟨a, ha, hopa⟩ := hand
  obtain ⟨o, ho, hopo⟩ := hor
  by_contra hsize
  have hlen : C.gates.length ≤ 1 := by
    change ¬ 2 ≤ C.gates.length at hsize
    omega
  cases hgs : C.gates with
  | nil => simpa [hgs] using ha
  | cons g gs =>
    have hlen' : gs.length = 0 := by
      rw [hgs, List.length_cons] at hlen
      omega
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero hlen'
    subst gs
    have hae : a = g := by simpa [hgs] using ha
    have hoe : o = g := by simpa [hgs] using ho
    subst a
    subst o
    rw [hopa] at hopo
    cases hopo

lemma size_ge_two_of_distinct_edges (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    2 ≤ C.size := by
  apply size_ge_two_of_and_or C
  · exact AndGate.has_and_of_nonempty_edge_function n G C ⟨a, b, hab⟩ hmono hcomp
  · exact OrGate.has_or_of_distinct_edges n G C a b c d hab hcd hne hmono hcomp



namespace CircuitMono

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def WireImp (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma wireImp_append {a b : List Bool} (h : WireImp a b)
    (u v : Bool) (huv : u = true → v = true) :
    WireImp (a ++ [u]) (b ++ [v]) := by
  obtain ⟨hab, h⟩ := h
  refine ⟨by simp [hab], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append a [u] false i hi,
      List.getD_append b [v] false i (by omega)]
    exact h i
  · rw [List.getD_append_right a [u] false i (by omega),
      List.getD_append_right b [v] false i (by omega), ← hab]
    cases hd : i - a.length with
    | zero => simpa using huv
    | succ k => simp

lemma gate_eval_mono {a b : List Bool} (h : WireImp a b) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq,
      List.all_eq_true]
    intro ha i hi
    exact h.2 i (ha i hi)
  · simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq,
      List.any_eq_true]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, h.2 i ha⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : WireImp a b) :
    WireImp (gs.foldl step a) (gs.foldl step b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact wireImp_append h _ _ (gate_eval_mono h g (hgs g (by simp)))

lemma circuit_eval_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  have hin : WireImp (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < n
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using hxy ⟨i, hi⟩
    · simp [List.getD_eq_getElem?_getD, hi]
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
  exact (fold_mono C.gates hgs _ _ hin).2 C.output

end CircuitMono

namespace Boundary

lemma independent_extend {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n))
    (hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) :
    ∃ J : Finset (Fin n), I ⊆ J ∧
      (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) ∧
      ∀ u, u ∉ J → ∃ v ∈ J, G.Adj u v := by
  classical
  let A : Finset (Finset (Fin n)) := Finset.univ.filter fun J =>
    I ⊆ J ∧ ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v
  have hA : A.Nonempty := by
    refine ⟨I, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.Subset.refl _, hI⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hJ' : I ⊆ J ∧ ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v :=
    (Finset.mem_filter.mp hJ).2
  refine ⟨J, hJ'.1, hJ'.2, ?_⟩
  intro u hu
  by_contra! hn
  have hins : ∀ a ∈ insert u J, ∀ b ∈ insert u J, ¬ G.Adj a b := by
    intro a ha b hb
    by_cases hau : a = u
    · subst a
      by_cases hbu : b = u
      · subst b
        exact G.loopless.irrefl u
      · exact hn b (by simpa only [Finset.mem_insert, hbu, false_or] using hb)
    · have haJ : a ∈ J := by
        simpa only [Finset.mem_insert, hau, false_or] using ha
      by_cases hbu : b = u
      · subst b
        exact fun hadj => hn a haJ hadj.symm
      · exact hJ'.2 a haJ b (by simpa only [Finset.mem_insert, hbu, false_or] using hb)
  have hmem : insert u J ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hJ'.1.trans (Finset.subset_insert _ _), hins⟩
  have hcard := hmax (insert u J) hmem
  rw [Finset.card_insert_of_notMem hu] at hcard
  omega

lemma complete {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hedge : ∀ u v, G.Adj u v →
      f (fun i => decide (i = u ∨ i = v)) = true)
    (hind : ∀ I : Finset (Fin n),
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      f (fun i => decide (i ∈ I)) = false) :
    ∀ x : Fin n → Bool,
      f x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  intro x
  constructor
  · intro hx
    by_contra! hno
    let I : Finset (Fin n) := Finset.univ.filter fun i => x i = true
    have hI : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
      intro u hu v hv hadj
      exact hno u v hadj (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2
    obtain ⟨J, hIJ, hJ, hmax⟩ := independent_extend G I hI
    have hup : ∀ i, x i = true → decide (i ∈ J) = true := by
      intro i hi
      exact decide_eq_true (hIJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    have htrue := hmono x (fun i => decide (i ∈ J)) hup hx
    have hfalse := hind J hJ hmax
    rw [hfalse] at htrue
    cases htrue
  · rintro ⟨u, v, hadj, hu, hv⟩
    apply hmono (fun i => decide (i = u ∨ i = v)) x
    · intro i hi
      rcases of_decide_eq_true hi with rfl | rfl
      · exact hu
      · exact hv
    · exact hedge u v hadj

end Boundary

lemma circuit_complete_of_boundary (n : ℕ) (G : SimpleGraph (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hedge : ∀ u v, G.Adj u v →
      C.eval (List.ofFn fun i => decide (i = u ∨ i = v)) = true)
    (hind : ∀ I : Finset (Fin n),
      (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
      C.eval (List.ofFn fun i => decide (i ∈ I)) = false) :
    ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  exact Boundary.complete G (fun x => C.eval (List.ofFn x))
    (fun x y hxy => CircuitMono.circuit_eval_mono n C hmono x y hxy) hedge hind


namespace PairOnly

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hood : Fin 6 → ℕ := ![14, 21, 35, 1, 2, 4]

abbrev adj (u v : Fin 6) : Prop := (hood u).testBit v.val = true

def graph : SimpleGraph (Fin 6) where
  Adj := adj
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def edges : Finset (Sym2 (Fin 6)) :=
  {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(1, 4), s(2, 5)}

lemma edges_eq : graph.edgeSet = (edges : Set (Sym2 (Fin 6))) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    change adj u v ↔ s(u, v) ∈ edges
    revert u v
    decide +kernel

lemma edge_count : graph.edgeSet.ncard = 6 := by
  rw [edges_eq, Set.ncard_coe_finset]
  decide +kernel

lemma no_four_cycle : ∀ a b c d : Fin 6, a ≠ c → b ≠ d →
    graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬ graph.Adj d a := by
  unfold graph
  decide +kernel

lemma has_cover : ∃ S : Finset (Fin 6),
    CoverPromise.IsVertexCover graph S ∧ S.card = 3 := by
  refine ⟨{0, 1, 2}, ?_, by decide +kernel⟩
  unfold CoverPromise.IsVertexCover graph
  decide +kernel

lemma cover_minimum : ∀ S : Finset (Fin 6),
    CoverPromise.IsVertexCover graph S → 3 ≤ S.card := by
  unfold CoverPromise.IsVertexCover graph
  decide +kernel

def circuit : Circuit where
  gates := [⟨.or, [0, 2]⟩, ⟨.or, [6, 4]⟩,
    ⟨.or, [0, 5]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [7, 11]⟩]
  output := 12

lemma circuit_monotone : Monotone2 circuit := by
  simp [Monotone2, circuit]

lemma circuit_size : circuit.size = 7 := rfl

lemma pair_agreement : ∀ u v : Fin 6,
    circuit.eval (List.ofFn (fun i => decide (i = u ∨ i = v))) = true ↔
      graph.Adj u v := by
  unfold graph
  decide +kernel

def bad : Fin 6 → Bool := fun i => decide (3 ≤ i.val)

lemma bad_accepted : circuit.eval (List.ofFn bad) = true := by
  decide +kernel

lemma bad_independent : ¬ ∃ u v : Fin 6,
    graph.Adj u v ∧ bad u = true ∧ bad v = true := by
  unfold graph
  decide +kernel

lemma below_bound : circuit.size + 1 < graph.edgeSet.ncard + 3 := by
  rw [circuit_size, edge_count]
  decide

end PairOnly

end PEqualNP.Outside.L_meta_2028
