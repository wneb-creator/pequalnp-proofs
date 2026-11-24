import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3821_aux.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact fold_length C.gates x

lemma wires_append (C : Circuit) (g : Gate) (x : List Bool) :
    (Circuit.mk (C.gates ++ [g]) 0).wires x =
      C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

def Represents (m : ℕ) (C : Circuit) (f : (Fin m → Bool) → Bool) : Prop :=
  ∃ i : ℕ, ∀ y : Fin m → Bool, (C.wires (List.ofFn y)).getD i false = f y

lemma represents_false (m : ℕ) (C : Circuit) :
    Represents m C (fun _ => false) := by
  refine ⟨m + C.size, ?_⟩
  intro y
  apply List.getD_eq_default
  simp [wires_length]

lemma represents_append (m : ℕ) (C : Circuit) (g : Gate)
    (f : (Fin m → Bool) → Bool) (h : Represents m C f) :
    Represents m (Circuit.mk (C.gates ++ [g]) 0) f := by
  obtain ⟨i, hi⟩ := h
  by_cases small : i < m + C.size
  · refine ⟨i, ?_⟩
    intro y
    rw [wires_append]
    rw [List.getD_append]
    · exact hi y
    · simpa [wires_length] using small
  · have eqfalse : f = fun _ => false := by
      funext y
      rw [← hi y]
      apply List.getD_eq_default
      simpa [wires_length] using Nat.le_of_not_gt small
    rw [eqfalse]
    exact represents_false m _

lemma append_gate_representation (m : ℕ) (C : Circuit) (g : Gate) :
    Represents m (Circuit.mk (C.gates ++ [g]) 0)
      (fun y : Fin m → Bool =>
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false)) := by
  refine ⟨m + C.size, ?_⟩
  intro y
  rw [wires_append]
  have hl : (C.wires (List.ofFn y)).length = m + C.size := by simp [wires_length]
  rw [← hl]
  simp

lemma append_legal (C : Circuit) (g : Gate) (hc : FanInTwo C)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    FanInTwo (Circuit.mk (C.gates ++ [g]) 0) := by
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hc q hq
  · exact hg

lemma fold_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false =
      x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    · exact List.getD_append _ _ _ _ hi
    · simp only [List.length_append, List.length_singleton]
      omega

lemma wires_input (m : ℕ) (C : Circuit) (i : Fin m) (y : Fin m → Bool) :
    (C.wires (List.ofFn y)).getD i false = y i := by
  rw [Circuit.wires, fold_input]
  · simp
  · simp

noncomputable def base (m : ℕ) : Finset ((Fin m → Bool) → Bool) :=
  insert (fun _ => false) (Finset.univ.image fun i : Fin m => fun y : Fin m → Bool => y i)

lemma represents_base (m : ℕ) (C : Circuit) (f : (Fin m → Bool) → Bool)
    (hf : f ∈ base m) : Represents m C f := by
  classical
  simp only [base, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hf
  rcases hf with rfl | ⟨i, rfl⟩
  · exact represents_false m C
  · exact ⟨i, wires_input m C i⟩

lemma extend_represented (m : ℕ) (C : Circuit) (hc : FanInTwo C)
    (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (fs : List ((Fin m → Bool) → Bool)) (hlen : fs.length ≤ 2)
    (hfs : ∀ f ∈ fs, Represents m C f) :
    ∃ E : Circuit, FanInTwo E ∧ E.size = C.size + 1 ∧
      Represents m E (fun y => op.eval (fs.map fun f => f y)) ∧
      ∀ f, Represents m C f → Represents m E f := by
  classical
  have hchoose : ∀ f : (Fin m → Bool) → Bool, f ∈ fs →
      ∃ i : ℕ, ∀ y, (C.wires (List.ofFn y)).getD i false = f y := hfs
  choose idx hidx using hchoose
  let args : List ℕ := fs.attach.map (fun f => idx f.val f.property)
  let g : Gate := ⟨op, args⟩
  refine ⟨⟨C.gates ++ [g], 0⟩, append_legal C g hc ?_, ?_, ?_, ?_⟩
  · exact ⟨hop, by simpa [g, args] using hlen⟩
  · simp [Circuit.size]
  · have heq : (fun y : Fin m → Bool =>
        g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn y)).getD i false)) =
        (fun y : Fin m → Bool => op.eval (fs.map fun f => f y)) := by
      funext y
      apply congrArg op.eval
      change (fs.attach.map (fun f => idx f.val f.property)).map
        (fun i => (C.wires (List.ofFn y)).getD i false) = fs.map (fun f => f y)
      simp only [List.map_map]
      calc
        fs.attach.map (fun f => (C.wires (List.ofFn y)).getD (idx f.val f.property) false) =
            fs.attach.map (fun f => f.val y) := by
          apply List.map_congr_left
          intro f hf
          exact hidx f.val f.property y
        _ = fs.map (fun f => f y) := by simp
    rw [← heq]
    exact append_gate_representation m C g
  · exact fun f hf => represents_append m C g f hf

lemma compile_step (m : ℕ) (S : Finset ((Fin m → Bool) → Bool))
    (C : Circuit) (hc : FanInTwo C) (hsize : C.size ≤ (S \ base m).card)
    (hrep : ∀ f ∈ S, Represents m C f)
    (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (fs : List ((Fin m → Bool) → Bool)) (hlen : fs.length ≤ 2)
    (hfs : ∀ f ∈ fs, f ∈ S ∪ base m) :
    let f := fun y => op.eval (fs.map fun g => g y)
    ∃ E : Circuit, FanInTwo E ∧ E.size ≤ (insert f S \ base m).card ∧
      ∀ g ∈ insert f S, Represents m E g := by
  classical
  dsimp only
  let f := fun y => op.eval (fs.map fun g => g y)
  by_cases old : f ∈ S ∪ base m
  · refine ⟨C, hc, ?_, ?_⟩
    · exact hsize.trans (Finset.card_le_card (by intro g hg; simp_all))
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · rcases Finset.mem_union.mp old with hold | hbase
        · exact hrep f hold
        · exact represents_base m C f hbase
      · exact hrep g hg
  · have hinputs : ∀ g ∈ fs, Represents m C g := by
      intro g hg
      rcases Finset.mem_union.mp (hfs g hg) with hold | hbase
      · exact hrep g hold
      · exact represents_base m C g hbase
    obtain ⟨E, hE, hlenE, hnew, hprior⟩ := extend_represented m C hc op hop fs hlen hinputs
    refine ⟨E, hE, ?_, ?_⟩
    · have hnotbase : f ∉ base m := fun hf => old (Finset.mem_union_right S hf)
      have hnots : f ∉ S := fun hf => old (Finset.mem_union_left _ hf)
      rw [show (fun y => op.eval (fs.map fun g => g y)) = f from rfl]
      rw [Finset.insert_sdiff_of_notMem _ hnotbase,
        Finset.card_insert_of_notMem (by simp [hnots]), hlenE]
      exact Nat.add_le_add_right hsize 1
    · intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hnew
      · exact hprior g (hrep g hg)

end PEqualNP.Outside.L_meta_3821_aux.Compression
