import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.Merge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def fold {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [op g.op (g.inputs.map fun i => w.getD i d)]) w

lemma fold_append {α : Type} (d : α) (op : GateOp → List α → α)
    (gs hs : List Gate) (w : List α) :
    fold d op (gs ++ hs) w = fold d op hs (fold d op gs w) := by
  simp [fold, List.foldl_append]

lemma fold_snoc {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (g : Gate) (w : List α) :
    fold d op (gs ++ [g]) w = fold d op gs w ++
      [op g.op (g.inputs.map fun i => (fold d op gs w).getD i d)] := by
  rw [fold_append]
  rfl

lemma fold_length {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : (fold d op gs w).length = w.length + gs.length :=
  Star.scan_length _ _ _

lemma fold_input {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) (i : ℕ) (hi : i < w.length) :
    (fold d op gs w).getD i d = w.getD i d := Star.scan_prefix _ _ _ _ _ hi

lemma fold_shift {α : Type} (d : α) (op : GateOp → List α → α) (F init : List α) (n s : ℕ)
    (hinit : init.length = n) (hF : F.length = n + s) (hFi : ∀ i < n, F.getD i d = init.getD i d)
    (H : List Gate) : ∀ u, (fold d op (H.map (shGate n s)) F).getD (shIdx n s u) d =
      (fold d op H init).getD u d := by
  induction H using List.reverseRecOn with
  | nil =>
    intro u
    simp only [List.map_nil, fold, List.foldl_nil]
    unfold shIdx
    split_ifs with h
    · exact hFi u h
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton H g ih =>
    intro u
    rw [List.map_append, List.map_singleton, fold_snoc, fold_snoc]
    have hA := fold_length d op (H.map (shGate n s)) F
    have hB := fold_length d op H init
    simp only [List.length_map] at hA
    have ihu := ih u
    unfold shIdx at ihu ⊢
    split_ifs with hu
    · rw [if_pos hu] at ihu
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ihu
    · rw [if_neg hu] at ihu
      rcases lt_trichotomy u (n + H.length) with h | h | h
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ihu
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [hA, hB, show u + s - (F.length + H.length) = 0 by omega,
          show u - (init.length + H.length) = 0 by omega]
        simp only [List.getD_cons_zero, shGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma concat_fold_right {α : Type} (d : α) (op : GateOp → List α → α)
    (n : ℕ) (C D : Circuit) (init : List α) (hn : init.length = n) (i : ℕ) :
    (fold d op (concat n C D).gates init).getD (shIdx n C.size i) d =
      (fold d op D.gates init).getD i d := by
  rw [concat, fold_append]
  apply fold_shift d op _ init n C.size hn
  · rw [fold_length, hn]
    rfl
  · intro j hj
    exact fold_input d op C.gates init j (by omega)

lemma concat_fold_left {α : Type} (d : α) (op : GateOp → List α → α)
    (n : ℕ) (C D : Circuit) (init : List α) (hn : init.length = n) (i : ℕ)
    (hi : i < n + C.size) :
    (fold d op (concat n C D).gates init).getD i d =
      (fold d op C.gates init).getD i d := by
  rw [concat, fold_append]
  apply fold_input
  simpa only [fold_length, hn, Circuit.size] using hi

lemma concat_eval (n : ℕ) (C D : Circuit) (x : List Bool) (hx : x.length = n) :
    (concat n C D).eval x = D.eval x :=
  concat_fold_right false GateOp.eval n C D x hx D.output

def readOp (S : List ℕ) (k : ℕ) : GateOp → List (List (List ℕ)) → List (List ℕ)
  | .or, ins => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and, ins => ins.foldl (andStep k) [S.map fun _ => 0]
  | _, _ => []

lemma readVectors_fold (n : ℕ) (C : Circuit) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = fold [] (readOp S k) C.gates ((List.range n).map (leafVectors S k)) := by
  unfold readVectors fold
  congr 1
  funext R g
  cases g.op <;> rfl

lemma concat_vectors_right (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ) :
    (readVectors (concat n C D) n S k).getD (concat n C D).output [] =
      (readVectors D n S k).getD D.output [] := by
  rw [readVectors_fold, readVectors_fold]
  exact concat_fold_right [] (readOp S k) n C D ((List.range n).map (leafVectors S k)) (by simp) D.output

lemma concat_vectors_left (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ)
    (hC : C.output < n + C.size) :
    (readVectors (concat n C D) n S k).getD C.output [] =
      (readVectors C n S k).getD C.output [] := by
  rw [readVectors_fold, readVectors_fold]
  exact concat_fold_left [] (readOp S k) n C D ((List.range n).map (leafVectors S k)) (by simp) C.output hC

def unionCircuit (n : ℕ) (C D : Circuit) : Circuit :=
  Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output

lemma union_size (n : ℕ) (C D : Circuit) :
    (unionCircuit n C D).size = C.size + D.size + 1 := by
  rw [unionCircuit, Star.addGate_size, concat_size]

lemma union_output (n : ℕ) (C D : Circuit) :
    (unionCircuit n C D).output < n + (unionCircuit n C D).size := by
  simp [unionCircuit, Star.addGate, Circuit.size]

lemma union_valid (n : ℕ) (C D : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hD : PEqualNP.TopForm.IsAO2 n D)
    (hoC : C.output < n + C.size) (hoD : D.output < n + D.size) :
    PEqualNP.TopForm.IsAO2 n (unionCircuit n C D) := by
  apply Star.addGate_valid
  · exact concat_valid n C D hC hD
  · exact Or.inr rfl
  · rw [concat_size]
    omega
  · exact concat_output n C D hoD

lemma union_eval (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (x : List Bool) (hx : x.length = n) :
    (unionCircuit n C D).eval x = (C.eval x || D.eval x) := by
  rw [unionCircuit, Star.addGate_eval n _ _ _ _ x hx]
  have hleft : ((concat n C D).wires x).getD C.output false = C.eval x :=
    concat_fold_left false GateOp.eval n C D x hx C.output hC
  have hright : ((concat n C D).wires x).getD (concat n C D).output false = D.eval x :=
    concat_eval n C D x hx
  simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, hleft, hright]

lemma union_read_left (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (S : List ℕ) (k : ℕ) (hr : readsAtMost C n S k = true) :
    readsAtMost (unionCircuit n C D) n S k = true := by
  obtain ⟨v, hv, hread⟩ := List.any_eq_true.mp hr
  apply List.any_eq_true.mpr
  refine ⟨v, ?_, hread⟩
  change v ∈ (readVectors (Star.addGate n (concat n C D) GateOp.or C.output
    (concat n C D).output) n S k).getD
    (Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output).output []
  rw [Star.addGate_vectors]
  apply Star.mem_rstep_or
  left
  rw [concat_vectors_left n C D S k hC]
  exact hv

lemma union_read_right (n : ℕ) (C D : Circuit) (S : List ℕ) (k : ℕ)
    (hr : readsAtMost D n S k = true) :
    readsAtMost (unionCircuit n C D) n S k = true := by
  obtain ⟨v, hv, hread⟩ := List.any_eq_true.mp hr
  apply List.any_eq_true.mpr
  refine ⟨v, ?_, hread⟩
  change v ∈ (readVectors (Star.addGate n (concat n C D) GateOp.or C.output
    (concat n C D).output) n S k).getD
    (Star.addGate n (concat n C D) GateOp.or C.output (concat n C D).output).output []
  rw [Star.addGate_vectors]
  apply Star.mem_rstep_or
  right
  rw [concat_vectors_right]
  exact hv

lemma union_read_one (n : ℕ) (C D : Circuit) (hC : C.output < n + C.size)
    (rC : IsReadK n C 1) (rD : IsReadK n D 1) :
    IsReadK n (unionCircuit n C D) 1 := by
  intro S hS
  have heval := hS.1
  change (unionCircuit n C D).eval (List.ofFn (setInput S)) = true at heval
  rw [union_eval n C D hC _ (by simp), Bool.or_eq_true] at heval
  have hprime (T : Finset (Fin n)) (hT : T ∈ S.ssubsets) :
      C.eval (List.ofFn (setInput T)) = false ∧ D.eval (List.ofFn (setInput T)) = false := by
    have hf := hS.2 T hT
    change (unionCircuit n C D).eval (List.ofFn (setInput T)) = false at hf
    rw [union_eval n C D hC _ (by simp)] at hf
    cases hc : C.eval (List.ofFn (setInput T)) <;>
      cases hd : D.eval (List.ofFn (setInput T)) <;> simp_all
  rcases heval with heval | heval
  · apply union_read_left n C D hC
    exact rC S ⟨heval, fun T hT => (hprime T hT).1⟩
  · apply union_read_right n C D
    exact rD S ⟨heval, fun T hT => (hprime T hT).2⟩

end PEqualNP.Outside.L_meta_2585.Merge
