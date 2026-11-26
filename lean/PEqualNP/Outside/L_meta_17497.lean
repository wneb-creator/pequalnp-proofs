import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17497

def Normal {n : Nat} (L : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ i < L.length, ∃ (a b : List (Fin n)) (p q : List Nat), ∀ x : Fin n → Bool,
    L.getD i (fun _ => false) x =
      ((a.any x || p.any (fun j => (L.take i).getD j (fun _ => false) x)) &&
       (b.any x || q.any (fun j => (L.take i).getD j (fun _ => false) x)))

theorem normal_nil {n : Nat} : Normal ([] : List ((Fin n → Bool) → Bool)) := by
  intro i hi
  simp at hi

theorem normal_append {n : Nat} {L : List ((Fin n → Bool) → Bool)}
    {f : (Fin n → Bool) → Bool} (hL : Normal L)
    (h : ∃ (a b : List (Fin n)) (p q : List Nat), ∀ x : Fin n → Bool,
      f x = ((a.any x || p.any (fun j => L.getD j (fun _ => false) x)) &&
             (b.any x || q.any (fun j => L.getD j (fun _ => false) x)))) :
    Normal (L ++ [f]) := by
  intro i hi
  by_cases hlt : i < L.length
  · rw [List.take_append_of_le_length hlt.le, List.getD_append _ _ _ _ hlt]
    exact hL i hlt
  · have ei : i = L.length := by simp at hi; omega
    subst i
    simpa only [List.take_left, List.getD_append_right _ _ _ _ (le_refl _),
      Nat.sub_self, List.getD_cons_zero] using h

theorem init_or {n : ℕ} (j : ℕ) :
    ∃ (I : List (Fin n)) (J : List ℕ), (∀ a ∈ J, a < 0) ∧ ∀ x : Fin n → Bool,
      (List.ofFn x).getD j false =
        (I.any x || J.any fun a => ([] : List ((Fin n → Bool) → Bool)).getD a (fun _ => false) x) := by
  by_cases hj : j < n
  · exact ⟨[⟨j, hj⟩], [], by simp, fun x => by simp [hj]⟩
  · exact ⟨[], [], by simp, fun x => by
      rw [List.getD_eq_default _ _ (by simp; omega)]
      rfl⟩

theorem read_append {n : ℕ} {L : List ((Fin n → Bool) → Bool)} {f : (Fin n → Bool) → Bool}
    {x : Fin n → Bool} {J : List ℕ} (h : ∀ j ∈ J, j < L.length) :
    (J.any fun j => (L ++ [f]).getD j (fun _ => false) x) =
      (J.any fun j => L.getD j (fun _ => false) x) := by
  induction J with
  | nil => rfl
  | cons j js ih =>
    simp only [List.any_cons, List.getD_append _ _ _ _ (h j List.mem_cons_self)]
    rw [ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BitFn (n : ℕ) := (Fin n → Bool) → Bool

def off {n} : BitFn n := fun _ => false

def expr {n} (L : List (BitFn n)) (I : List (Fin n)) (J : List ℕ) (x : Fin n → Bool) :=
  I.any x || J.any fun j => L.getD j off x

def Form {n} (L : List (BitFn n)) (f : BitFn n) : Prop :=
  ∃ (I : List (Fin n)) (J : List ℕ), (∀ j ∈ J, j < L.length) ∧ ∀ x, f x = expr L I J x

def Covers {n} (L W : List (BitFn n)) : Prop :=
  ∀ j : ℕ, Form L (W.getD j off)

theorem form_zero {n} (L : List (BitFn n)) : Form L off := by
  exact ⟨[],[],by simp,by simp [off, expr]⟩

theorem cover_snoc {n} {L W : List (BitFn n)} (f : BitFn n)
    (hc : Covers L W) (hf : Form L f) : Covers L (W ++ [f]) := by
  intro j
  by_cases hj : j = W.length
  · subst j
    simpa using hf
  · by_cases inside : j < W.length
    · rw [List.getD_append _ _ _ _ inside]
      exact hc j
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      exact form_zero _

theorem cover_extend {n} {L W : List (BitFn n)} (f : BitFn n) (hc : Covers L W) :
    Covers (L ++ [f]) W := by
  intro j
  obtain ⟨I,J,hJ,h⟩ := hc j
  refine ⟨I,J,fun a ha => by simpa using Nat.lt_succ_of_lt (hJ a ha), ?_⟩
  intro x
  rw [h]
  exact congrArg (fun b => I.any x || b) (read_append (L := L) (f := f) (x := x) hJ).symm

def opFn {n} (W : List (BitFn n)) (g : Gate) : BitFn n := fun x =>
  g.op.eval (g.inputs.map fun i => W.getD i off x)

def runFns {n} (gs : List Gate) (W : List (BitFn n)) : List (BitFn n) :=
  gs.foldl (fun W g => W ++ [opFn W g]) W

noncomputable def countAnd (g : Gate) : Bool :=
  g.op.rec true false false (fun _ => false) false

-- Each wire is represented by a disjunction of raw inputs and registered AND outputs.
-- OR concatenates the two lists of summands. AND records one new function, which
-- subsequent wires may refer to by its index.
theorem build {n} (gs : List Gate)
    (allowed : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (L W : List (BitFn n)) (hL : Normal L) (hc : Covers L W) :
    ∃ L' : List (BitFn n), Normal L' ∧ L'.length = L.length + gs.countP countAnd ∧
      Covers L' (runFns gs W) := by
  induction gs generalizing L W with
  | nil => exact ⟨L,hL,by simp,hc⟩
  | cons g gs ih =>
    have ⟨hop,hlen⟩ := allowed g List.mem_cons_self
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hlen
    obtain ⟨Ia,Ja,HJa,ha⟩ := hc a
    obtain ⟨Ib,Jb,HJb,hb⟩ := hc b
    have ht := fun t ht => allowed t (List.mem_cons_of_mem g ht)
    rcases hop with op | op
    · have gate (x : Fin n → Bool) : opFn W g x = (expr L Ia Ja x && expr L Ib Jb x) := by
        simp only [opFn, op, hab, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, id_eq, Bool.and_true, ha, hb]
      have hn := normal_append (f := opFn W g) hL ⟨Ia, Ib, Ja, Jb, gate⟩
      have own : Form (L ++ [opFn W g]) (opFn W g) := by
        exact ⟨[],[L.length],by simp,by simp [expr]⟩
      obtain ⟨L',hN,hS,hC⟩ := ih ht _ _ hn (cover_snoc _ (cover_extend _ hc) own)
      refine ⟨L',hN,?_,hC⟩
      simpa [countAnd, op, List.countP_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hS
    · have gate : Form L (opFn W g) := by
        refine ⟨Ia ++ Ib,Ja ++ Jb,?_,?_⟩
        · intro j hj
          exact (List.mem_append.mp hj).elim (HJa j) (HJb j)
        · intro x
          simp only [opFn, op, hab, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ha, hb, expr, List.any_append]
          ac_rfl
      obtain ⟨L',hN,hS,hC⟩ := ih ht _ _ hL (cover_snoc _ hc gate)
      refine ⟨L',hN,?_,hC⟩
      simpa [countAnd, op, List.countP_cons] using hS

theorem lookup_values {n} (W : List (BitFn n)) (j : ℕ) (x : Fin n → Bool) :
    (W.map (fun f => f x)).getD j false = W.getD j off x := by
  induction W generalizing j with
  | nil => simp [off]
  | cons f W ih => cases j with
    | zero => rfl
    | succ k => exact ih k

theorem run_values {n} (gs : List Gate) (W : List (BitFn n)) (x : Fin n → Bool) :
    (runFns gs W).map (fun f => f x) =
      gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)])
        (W.map fun f => f x) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    change ((runFns gs (W ++ [opFn W g])).map _) = gs.foldl _ _
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, opFn, lookup_values]

def inputFns (n : ℕ) : List (BitFn n) := List.ofFn fun i x => x i

theorem input_values {n} (x : Fin n → Bool) : (inputFns n).map (fun f => f x) = List.ofFn x := by
  simp [inputFns, List.map_ofFn, Function.comp_def]

theorem decompose (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    ∃ L : List (BitFn n), L.length = C.gates.countP countAnd ∧ Normal L ∧
      ∃ (I : List (Fin n)) (J : List ℕ), ∀ x, circuitFun n C x = expr L I J x := by
  have init : Covers ([] : List (BitFn n)) (inputFns n) := by
    intro j
    obtain ⟨I,J,hJ,hx⟩ := init_or (n := n) j
    refine ⟨I,J,hJ,?_⟩
    intro x
    rw [← lookup_values, input_values]
    exact hx x
  obtain ⟨L,hL,hs,hc⟩ := build C.gates (fun g hg => ⟨h.1 g hg, h.2.2 g hg⟩) [] (inputFns n)
    normal_nil init
  obtain ⟨I,J,_,hJ⟩ := hc C.output
  refine ⟨L,by simpa using hs,hL,I,J,?_⟩
  intro x
  rw [← hJ x, ← lookup_values, run_values, input_values]
  rfl

end PEqualNP.Outside.L_meta_17497

theorem PEqualNP.Outside.L_meta_17497 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x4 : List ((Fin x1 → Bool) → Bool)), x4.length = List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x2.gates ∧ (∀ x5 < x4.length, ∃ (x7 : List (Fin x1)) (x8 : List (Fin x1)) (x9 : List ℕ) (x10 : List ℕ), ∀ (x11 : Fin x1 → Bool), x4.getD x5 (fun (x12 : Fin x1 → Bool) => Bool.false) x11 = ((x7.any x11 || x9.any fun (x12 : ℕ) => (List.take x5 x4).getD x12 (fun (x13 : Fin x1 → Bool) => Bool.false) x11) && (x8.any x11 || x10.any fun (x12 : ℕ) => (List.take x5 x4).getD x12 (fun (x13 : Fin x1 → Bool) => Bool.false) x11))) ∧ ∃ (x5 : List (Fin x1)) (x6 : List ℕ), ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x7 = (x5.any x7 || x6.any fun (x8 : ℕ) => x4.getD x8 (fun (x9 : Fin x1 → Bool) => Bool.false) x7) := by
  exact L_meta_17497.decompose
