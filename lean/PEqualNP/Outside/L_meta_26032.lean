import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26032_aux

namespace FullRefutation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

private theorem zmod2_add_self (t : ZMod 2) : t + t = 0 := by
  revert t
  decide

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem b2z_decide_eq_one (t : ZMod 2) : b2z (decide (t = 1)) = t := by
  revert t
  decide

private theorem gate_eval_one_affine (op : GateOp) :
    ∃ c0 c1 : ZMod 2, ∀ x : Bool, b2z (op.eval [x]) = c0 + c1 * b2z x := by
  refine ⟨b2z (op.eval [false]), b2z (op.eval [true]) + b2z (op.eval [false]), fun x => ?_⟩
  cases x
  · simp [b2z]
  · simp only [b2z, ↓reduceIte, mul_one]
    generalize op.eval [false] = a
    generalize op.eval [true] = b
    cases a <;> cases b <;> decide

private theorem gate_eval_two_poly (op : GateOp) :
    ∃ c0 c1 c2 : ZMod 2, ∀ x y : Bool,
      b2z (op.eval [x, y]) = c0 + c1 * b2z x + c2 * b2z y +
        b2z (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2z x * b2z y) := by
  refine ⟨b2z (op.eval [false, false]),
    b2z (op.eval [true, false]) + b2z (op.eval [false, false]),
    b2z (op.eval [false, true]) + b2z (op.eval [false, false]), fun x y => ?_⟩
  cases x <;> cases y <;>
  · generalize op.eval [false, false] = a
    generalize op.eval [false, true] = b
    generalize op.eval [true, false] = c
    generalize op.eval [true, true] = d
    cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

private theorem mem_le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) :
    a ≤ l.foldr max 0 :=
  (foldr_max_le_iff l (l.foldr max 0)).1 (le_refl _) a ha

private def runFold {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun l g => l ++ [step l g]) init

private theorem runFold_length {α : Type} (step : List α → Gate → α) (init : List α) (gs : List Gate) :
    (runFold step init gs).length = init.length + gs.length := by
  unfold runFold
  induction gs generalizing init with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private theorem runFold_append {α : Type} (step : List α → Gate → α) (init : List α)
    (gs1 gs2 : List Gate) :
    runFold step init (gs1 ++ gs2) = runFold step (runFold step init gs1) gs2 := by
  unfold runFold
  exact List.foldl_append

private theorem getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d0 : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d0 = l1.getD i d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_ge {α : Type} (l : List α) (i : ℕ) (d0 : α) (hi : l.length ≤ i) :
    l.getD i d0 = d0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

private theorem runFold_getD_prefix {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (w : ℕ) (d0 : α) (hw : w < init.length) :
    (runFold step init gs).getD w d0 = init.getD w d0 := by
  unfold runFold
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hw' : w < (init ++ [step init g]).length := by
      rw [List.length_append, List.length_singleton]; omega
    rw [ih (init ++ [step init g]) hw', getD_append_left _ _ _ _ hw]

private theorem runFold_getD_gate {α : Type} (step : List α → Gate → α) (init : List α)
    (gs : List Gate) (idx : ℕ) (hidx : idx < gs.length) (d0 : α) :
    (runFold step init gs).getD (init.length + idx) d0 =
      step (runFold step init (gs.take idx)) (gs[idx]) := by
  have hsplit : gs = gs.take idx ++ [gs[idx]] ++ gs.drop (idx + 1) := by
    conv_lhs => rw [← List.take_append_drop idx gs]
    rw [List.append_assoc, List.singleton_append]
    congr 1
    exact (List.cons_getElem_drop_succ (h := hidx)).symm
  conv_lhs => rw [hsplit]
  rw [runFold_append, runFold_append]
  have hlen_take : (runFold step init (gs.take idx)).length = init.length + idx := by
    rw [runFold_length, List.length_take, min_eq_left (le_of_lt hidx)]
  have hlen1 : init.length + idx < (runFold step (runFold step init (gs.take idx)) [gs[idx]]).length := by
    rw [runFold_length, hlen_take, List.length_singleton]; omega
  rw [runFold_getD_prefix step _ (gs.drop (idx + 1)) (init.length + idx) d0 hlen1]
  unfold runFold
  simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD]
  have heq : init.length + idx = (gs.take idx |>.foldl (fun l g => l ++ [step l g]) init).length :=
    hlen_take.symm
  rw [List.getElem?_append_right (le_of_eq heq.symm), Nat.sub_eq_zero_of_le (le_of_eq heq)]
  rfl

private theorem wires_eq_runFold (C : Circuit) (x : List Bool) :
    C.wires x = runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates :=
  rfl

private theorem depths_eq_runFold (width : ℕ) (C : Circuit) :
    depths width C = runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate width 0) C.gates :=
  rfl

private theorem oneEach_length {n m : ℕ} (a : Fin n) (b : Fin m) :
    (oneEach a b).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ) (hw : w < n) :
    (oneEach a b).getD w false = decide ((⟨w, hw⟩ : Fin n) = a) := by
  unfold oneEach
  rw [getD_append_left _ _ _ _ (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem oneEach_getD_right {n m : ℕ} (a : Fin n) (b : Fin m) (w : ℕ)
    (hlo : n ≤ w) (hhi : w < n + m) :
    (oneEach a b).getD w false = decide ((⟨w - n, by omega⟩ : Fin m) = b) := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [hlo])]
  simp only [List.length_ofFn]
  have hlt : w - n < m := by omega
  simp [hlt]

private theorem gateAt_eq_getElem (C : Circuit) (idx : ℕ) (hidx : idx < C.gates.length) :
    gateAt C idx = C.gates[idx] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hidx]

private theorem wires_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (a : Fin n) (b : Fin m) (idx : ℕ) (hidx : idx < C.gates.length) :
    (C.wires (oneEach a b)).getD (n + m + idx) false =
      C.gates[idx].op.eval (C.gates[idx].inputs.map fun i => (C.wires (oneEach a b)).getD i false) := by
  rw [wires_eq_runFold]
  have hlen : (oneEach a b).length = n + m := oneEach_length a b
  have h1 := runFold_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    (oneEach a b) C.gates idx hidx false
  rw [hlen] at h1
  rw [h1]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      (oneEach a b) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i false hlt2).symm

private theorem depths_getD_gate {n m : ℕ} (C : Circuit) (hRB : ReadsBack (n + m) C)
    (idx : ℕ) (hidx : idx < C.gates.length) :
    (depths (n + m) C).getD (n + m + idx) 0 =
      (C.gates[idx].inputs.map fun i => (depths (n + m) C).getD i 0).foldr max 0 +
        (nonlinear C.gates[idx]).toNat := by
  rw [depths_eq_runFold]
  have hlen : (List.replicate (n + m) 0).length = n + m := List.length_replicate
  have h1 := runFold_getD_gate (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
    (List.replicate (n + m) 0) C.gates idx hidx 0
  rw [hlen] at h1
  rw [h1]
  congr 2
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < n + m + idx := by
    have hrb := hRB idx hidx i
    rw [gateAt_eq_getElem C idx hidx] at hrb
    exact hrb hi
  have htake : C.gates = C.gates.take idx ++ C.gates.drop idx := (List.take_append_drop idx C.gates).symm
  conv_rhs => rw [htake, runFold_append]
  have hlt2 : i < (runFold (fun ds g =>
      (g.inputs.map fun a => ds.getD a 0).foldr max 0 + (nonlinear g).toNat)
      (List.replicate (n + m) 0) (C.gates.take idx)).length := by
    rw [runFold_length, hlen, List.length_take, min_eq_left (le_of_lt hidx)]
    exact hlt
  exact (runFold_getD_prefix _ _ (C.gates.drop idx) i 0 hlt2).symm

private theorem depths_getD_input (width : ℕ) (C : Circuit) (w : ℕ) (hw : w < width) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, runFold_getD_prefix _ _ _ w 0 (by simp [hw])]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem depths_getD_oob (width : ℕ) (C : Circuit) (w : ℕ) (hw : width + C.gates.length ≤ w) :
    (depths width C).getD w 0 = 0 := by
  rw [depths_eq_runFold, getD_of_ge _ w 0]
  rw [runFold_length, List.length_replicate]
  exact hw

private theorem matrix_rank_zero {n m : ℕ} :
    (0 : Matrix (Fin n) (Fin m) (ZMod 2)).rank = 0 := by
  simp [Matrix.rank]

private theorem matrix_rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    have hsum : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by simp
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono : Module.finrank (ZMod 2) (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
    Submodule.finrank_mono hle
  omega

private theorem matrix_rank_sum_le {ι : Type} [DecidableEq ι] {n m : ℕ}
    (S : Finset ι) (f : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    (∑ i ∈ S, f i).rank ≤ ∑ i ∈ S, (f i).rank := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (matrix_rank_add_le _ _) (Nat.add_le_add_left ih _)

private theorem matrix_rank_decomp {n m : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ∃ (a : Fin B.rank → Fin n → ZMod 2) (b : Fin B.rank → Fin m → ZMod 2),
      B = ∑ k : Fin B.rank, Matrix.vecMulVec (a k) (b k) := by
  let bas := Module.finBasis (ZMod 2) (LinearMap.range B.mulVecLin)
  let a : Fin B.rank → Fin n → ZMod 2 := fun k => (bas k).1
  let b : Fin B.rank → Fin m → ZMod 2 := fun k j =>
    bas.repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ k
  refine ⟨a, b, ?_⟩
  ext i j
  have hcol : B.mulVecLin (Pi.single j 1) = ∑ k : Fin B.rank, (b k j) • (a k) := by
    have h1 := bas.sum_repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    exact h2.symm
  have hi := congrFun hcol i
  have hlhs : B.mulVecLin (Pi.single j 1) i = B i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hlhs] at hi
  rw [hi, Matrix.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun a b => M a b + M a v + M u b + M u v

private theorem anchor_zero {n m : ℕ} (u : Fin n) (v : Fin m) :
    anchor u v (0 : Matrix (Fin n) (Fin m) (ZMod 2)) = 0 := by
  ext a b; simp [anchor]

private theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m)
    (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (A + B) = anchor u v A + anchor u v B := by
  ext a b; simp only [anchor, Matrix.add_apply]; ring

private theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (c • A) = c • anchor u v A := by
  ext a b; simp only [anchor, Matrix.smul_apply, smul_eq_mul]; ring

private def IsSep {n m : ℕ} (M : Matrix (Fin n) (Fin m) (ZMod 2)) : Prop :=
  ∃ (α : Fin n → ZMod 2) (β : Fin m → ZMod 2), ∀ a b, M a b = α a + β b

private theorem anchor_of_isSep {n m : ℕ} (u : Fin n) (v : Fin m)
    {M : Matrix (Fin n) (Fin m) (ZMod 2)} (hM : IsSep M) :
    anchor u v M = 0 := by
  obtain ⟨α, β, h⟩ := hM
  ext a b
  simp only [anchor, h, Matrix.zero_apply]
  calc α a + β b + (α a + β v) + (α u + β b) + (α u + β v)
      = (α a + α a) + (α u + α u) + (β b + β b) + (β v + β v) := by ring
    _ = 0 := by simp [zmod2_add_self]

private theorem isSep_const {n m : ℕ} (c : ZMod 2) :
    IsSep (Matrix.of (fun (_ : Fin n) (_ : Fin m) => c)) :=
  ⟨fun _ => c, fun _ => 0, fun _ _ => by simp⟩

private theorem isSep_add {n m : ℕ} {A B : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) (hB : IsSep B) : IsSep (A + B) := by
  obtain ⟨α1, β1, h1⟩ := hA
  obtain ⟨α2, β2, h2⟩ := hB
  refine ⟨fun a => α1 a + α2 a, fun b => β1 b + β2 b, fun a b => ?_⟩
  simp only [Matrix.add_apply, h1, h2]
  ring

private theorem isSep_smul {n m : ℕ} (c : ZMod 2) {A : Matrix (Fin n) (Fin m) (ZMod 2)}
    (hA : IsSep A) : IsSep (c • A) := by
  obtain ⟨α, β, h⟩ := hA
  refine ⟨fun a => c * α a, fun b => c * β b, fun a b => ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, h]
  ring

private theorem anchor_vecMulVec_rank_le_one {n m : ℕ} (u : Fin n) (v : Fin m)
    (α : Fin n → ZMod 2) (β : Fin m → ZMod 2) :
    (anchor u v (Matrix.vecMulVec α β)).rank ≤ 1 := by
  have heq : anchor u v (Matrix.vecMulVec α β) =
      Matrix.vecMulVec (fun a => α a + α u) (fun b => β b + β v) := by
    ext a b
    simp only [anchor, Matrix.vecMulVec_apply]
    ring
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

private theorem countP_eq_card_filter {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = ((Finset.univ : Finset (Fin l.length)).filter (fun idx => p l[idx.val] = true)).card := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons, ih, Finset.card_filter, Finset.card_filter]
    have hs : ∑ idx : Fin (xs.length + 1), (if p (x :: xs)[idx.val] = true then 1 else 0) =
        (if p x = true then 1 else 0) + ∑ idx : Fin xs.length, (if p xs[idx.val] = true then 1 else 0) :=
      Fin.sum_univ_succ (fun idx : Fin (xs.length + 1) => if p (x :: xs)[idx.val] = true then 1 else 0)
    change (∑ idx : Fin xs.length, if p xs[idx.val] = true then 1 else 0) +
        (if p x = true then 1 else 0) =
      ∑ idx : Fin (xs.length + 1), if p (x :: xs)[idx.val] = true then 1 else 0
    rw [hs, Nat.add_comm]

private theorem forward_aux {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit) (tap : Fin q → ℕ)
    (hRB : ReadsBack (n + m) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nonlinear ≤ t)
    (htap : ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧ Represents (G j) ⟨C.gates, tap j⟩) :
    let F := ZMod 2
    let Mask := Fin q → F
    let Mat := Matrix (Fin n) (Fin m) F
    let entry := fun j a b => if G j a b then (1 : F) else 0
    let anchored : Fin q → Mat := fun j a b =>
      entry j a b + entry j a v + entry j u b + entry j u v
    ∃ N : ℕ, ∃ J : Finset (Fin N), ∃ M : Fin N → Mat,
      ∃ coeff : Fin q → Fin N → F, J.card ≤ t ∧
        (∀ i ∈ J, (M i).rank ≤ 2) ∧
        ∀ j : Fin q, anchored j = ∑ i ∈ J, coeff j i • M i := by
  intro F Mask Mat entry anchored
  let N := C.gates.length
  let val : ℕ → Mat := fun w a b => b2z ((C.wires (oneEach a b)).getD w false)
  let dep : ℕ → ℕ := fun w => (depths (n + m) C).getD w 0
  have hval_in_left : ∀ w < n, IsSep (val w) := by
    intro w hw
    refine ⟨fun a => b2z (decide ((⟨w, hw⟩ : Fin n) = a)), fun _ => 0, fun a b => ?_⟩
    simp only [val, wires_eq_runFold]
    rw [runFold_getD_prefix _ _ _ w false (by rw [oneEach_length]; omega),
      oneEach_getD_left a b w hw, add_zero]
  have hval_in_right : ∀ w, n ≤ w → w < n + m → IsSep (val w) := by
    intro w hlo hhi
    refine ⟨fun _ => 0, fun b => b2z (decide ((⟨w - n, by omega⟩ : Fin m) = b)), fun a b => ?_⟩
    simp only [val, wires_eq_runFold]
    rw [runFold_getD_prefix _ _ _ w false (by rw [oneEach_length]; omega),
      oneEach_getD_right a b w hlo hhi, zero_add]
  have hval_oob : ∀ w, n + m + N ≤ w → val w = 0 := by
    intro w hw
    ext a b
    simp only [val, wires_eq_runFold]
    rw [getD_of_ge _ w false (by rw [runFold_length, oneEach_length]; exact hw)]
    rfl
  have hdep0_sep : ∀ w : ℕ, dep w = 0 → IsSep (val w) := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hdep0
      by_cases hlt1 : w < n
      · exact hval_in_left w hlt1
      · by_cases hlt2 : w < n + m
        · exact hval_in_right w (by omega) hlt2
        · by_cases hlt3 : w < n + m + N
          · let idx := w - (n + m)
            have hidx : idx < C.gates.length := by omega
            have hw_eq : w = n + m + idx := by omega
            set g := C.gates[idx]
            have hdep_g : dep w = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat := by
              rw [hw_eq]
              exact depths_getD_gate C hRB idx hidx
            rw [hdep0] at hdep_g
            have hnl0 : (nonlinear g).toNat = 0 := by omega
            have hnl_false : nonlinear g = false := by
              cases h : nonlinear g
              · rfl
              · simp [h] at hnl0
            have hmax0 : (g.inputs.map dep).foldr max 0 = 0 := by omega
            have hin_dep0 : ∀ i ∈ g.inputs, dep i = 0 := by
              intro i hi
              have hle : dep i ≤ 0 := by
                rw [← hmax0]
                exact mem_le_foldr_max (List.mem_map_of_mem hi)
              exact Nat.eq_zero_of_le_zero hle
            have hin_lt : ∀ i ∈ g.inputs, i < w := by
              intro i hi
              have hrb := hRB idx hidx i
              rw [gateAt_eq_getElem C idx hidx] at hrb
              have := hrb hi
              omega
            have hglen : g.inputs.length ≤ 2 := hfan g (List.getElem_mem hidx)
            have hval_g : ∀ a b, val w a b =
                b2z (g.op.eval (g.inputs.map fun i => (C.wires (oneEach a b)).getD i false)) := by
              intro a b
              simp only [val]
              rw [hw_eq, wires_getD_gate C hRB a b idx hidx]
            rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
            · refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun a b => ?_⟩
              rw [hval_g a b, hlist]; simp
            · obtain ⟨c0, c1, haff⟩ := gate_eval_one_affine g.op
              have hi1_sep : IsSep (val i1) :=
                ih i1 (hin_lt i1 (by simp [hlist])) (hin_dep0 i1 (by simp [hlist]))
              have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
                ext a b
                rw [hval_g a b, hlist]
                exact haff ((C.wires (oneEach a b)).getD i1 false)
              rw [hcomb]
              exact isSep_add (isSep_const c0) (isSep_smul c1 hi1_sep)
            · have hrest : rest = [] := by
                rw [hlist] at hglen
                cases rest with
                | nil => rfl
                | cons _ _ => simp at hglen
              subst hrest
              obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
              have hxor_false : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                unfold nonlinear at hnl_false
                rw [hlist] at hnl_false
                simpa using hnl_false
              have hi1_sep : IsSep (val i1) :=
                ih i1 (hin_lt i1 (by simp [hlist])) (hin_dep0 i1 (by simp [hlist]))
              have hi2_sep : IsSep (val i2) :=
                ih i2 (hin_lt i2 (by simp [hlist])) (hin_dep0 i2 (by simp [hlist]))
              have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 + c2 • val i2 := by
                ext a b
                rw [hval_g a b, hlist]
                have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
                  ((C.wires (oneEach a b)).getD i2 false)
                rw [hxor_false] at hp
                simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hp
                exact hp
              rw [hcomb]
              exact isSep_add (isSep_add (isSep_const c0) (isSep_smul c1 hi1_sep)) (isSep_smul c2 hi2_sep)
          · rw [hval_oob w (by omega)]
            exact isSep_const 0
  let NL1 : Finset (Fin N) :=
    Finset.univ.filter (fun idx => nonlinear C.gates[idx.val] = true ∧ dep (n + m + idx.val) = 1)
  have hNL1_le : NL1.card ≤ t := by
    have hsub : NL1 ⊆ Finset.univ.filter (fun idx : Fin N => nonlinear C.gates[idx.val] = true) := by
      intro idx hidx
      simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and] at hidx ⊢
      exact hidx.1
    calc NL1.card
        ≤ (Finset.univ.filter (fun idx : Fin N => nonlinear C.gates[idx.val] = true)).card :=
          Finset.card_le_card hsub
      _ = C.gates.countP nonlinear := (countP_eq_card_filter nonlinear C.gates).symm
      _ ≤ t := hcnt
  let Mgate : Fin N → Mat := fun idx => anchor u v (val (n + m + idx.val))
  have hMgate_rank : ∀ idx ∈ NL1, (Mgate idx).rank ≤ 2 := by
    intro idx hidx
    simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and] at hidx
    obtain ⟨hnl, hdep1⟩ := hidx
    set g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nonlinear at hnl
      simp only [Bool.and_eq_true, beq_iff_eq] at hnl
      exact hnl.1
    have hxor_true : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nonlinear at hnl
      simp only [Bool.and_eq_true, beq_iff_eq] at hnl
      exact hnl.2
    rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨_, _⟩⟩⟩
    · simp [hlist] at hlen2
    · simp [hlist] at hlen2
    · have hdep_g : dep (n + m + idx.val) = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat :=
        depths_getD_gate C hRB idx.val idx.isLt
      rw [hdep1, hnl, hlist] at hdep_g
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdep_g
      have hdi1 : dep i1 = 0 := by omega
      have hdi2 : dep i2 = 0 := by omega
      obtain ⟨α1, β1, h1⟩ := hdep0_sep i1 hdi1
      obtain ⟨α2, β2, h2⟩ := hdep0_sep i2 hdi2
      obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
      have hdecomp : Mgate idx =
          anchor u v (Matrix.vecMulVec α1 β2) + anchor u v (Matrix.vecMulVec α2 β1) := by
        have hsep_part : IsSep (Matrix.of fun (a : Fin n) (b : Fin m) =>
            c0 + c1 * (α1 a + β1 b) + c2 * (α2 a + β2 b) + (α1 a * α2 a + β1 b * β2 b)) := by
          refine ⟨fun a => c0 + c1 * α1 a + c2 * α2 a + α1 a * α2 a,
            fun b => c1 * β1 b + c2 * β2 b + β1 b * β2 b, fun a b => ?_⟩
          simp only [Matrix.of_apply]
          ring
        have hval_eq : val (n + m + idx.val) =
            (Matrix.vecMulVec α1 β2 + Matrix.vecMulVec α2 β1) +
            (Matrix.of fun (a : Fin n) (b : Fin m) =>
              c0 + c1 * (α1 a + β1 b) + c2 * (α2 a + β2 b) + (α1 a * α2 a + β1 b * β2 b)) := by
          ext a b
          have hw := wires_getD_gate C hRB a b idx.val idx.isLt
          have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
            ((C.wires (oneEach a b)).getD i2 false)
          rw [hxor_true] at hp
          have hv1 : b2z ((C.wires (oneEach a b)).getD i1 false) = α1 a + β1 b := h1 a b
          have hv2 : b2z ((C.wires (oneEach a b)).getD i2 false) = α2 a + β2 b := h2 a b
          change b2z ((C.wires (oneEach a b)).getD (n + m + idx.val) false) = _
          rw [hw, show C.gates[idx.val] = g from rfl, hlist]
          simp only [List.map_cons, List.map_nil]
          rw [hp, hv1, hv2]
          simp only [b2z, ↓reduceIte, one_mul, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.of_apply]
          ring
        change anchor u v (val (n + m + idx.val)) = _
        rw [hval_eq, anchor_add, anchor_add, anchor_of_isSep u v hsep_part, add_zero]
      rw [hdecomp]
      calc (anchor u v (Matrix.vecMulVec α1 β2) + anchor u v (Matrix.vecMulVec α2 β1)).rank
          ≤ (anchor u v (Matrix.vecMulVec α1 β2)).rank + (anchor u v (Matrix.vecMulVec α2 β1)).rank :=
            matrix_rank_add_le _ _
        _ ≤ 1 + 1 := Nat.add_le_add (anchor_vecMulVec_rank_le_one u v α1 β2)
            (anchor_vecMulVec_rank_le_one u v α2 β1)
        _ = 2 := rfl
    · simp [hlist] at hlen2
  have hdep1_span : ∀ w : ℕ, dep w ≤ 1 →
      ∃ coeff : Fin N → F, anchor u v (val w) = ∑ idx ∈ NL1, coeff idx • Mgate idx := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hdw
      by_cases h0 : dep w = 0
      · refine ⟨0, ?_⟩
        rw [anchor_of_isSep u v (hdep0_sep w h0)]
        simp
      · have hdw1 : dep w = 1 := by omega
        have hge : n + m ≤ w := by
          by_contra hlt
          have := depths_getD_input (n + m) C w (by omega)
          exact h0 this
        have hlt : w < n + m + N := by
          by_contra hge2
          have := depths_getD_oob (n + m) C w (by omega)
          exact h0 this
        let idx : Fin N := ⟨w - (n + m), by omega⟩
        have hw_eq : w = n + m + idx.val := by simp [idx]; omega
        set g := C.gates[idx.val]
        by_cases hnl : nonlinear g = true
        · have hmem : idx ∈ NL1 := by
            simp only [NL1, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hnl, by rw [← hw_eq]; exact hdw1⟩
          refine ⟨fun k => if k = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp [Mgate, hw_eq]
          · intro k _ hne; simp [hne]
          · intro hnot; exact False.elim (hnot hmem)
        · have hnl_false : nonlinear g = false := Bool.eq_false_iff.2 hnl
          have hdep_g : dep w = (g.inputs.map dep).foldr max 0 + (nonlinear g).toNat := by
            rw [hw_eq]; exact depths_getD_gate C hRB idx.val idx.isLt
          have hin_le1 : ∀ i ∈ g.inputs, dep i ≤ 1 := by
            intro i hi
            have hle := mem_le_foldr_max (List.mem_map_of_mem (f := dep) hi)
            omega
          have hin_lt : ∀ i ∈ g.inputs, i < w := by
            intro i hi
            have hrb := hRB idx.val idx.isLt i
            rw [gateAt_eq_getElem C idx.val idx.isLt] at hrb
            have := hrb hi
            omega
          have hglen : g.inputs.length ≤ 2 := hfan g (List.getElem_mem idx.isLt)
          have hval_g : ∀ a b, val w a b =
              b2z (g.op.eval (g.inputs.map fun i => (C.wires (oneEach a b)).getD i false)) := by
            intro a b
            simp only [val]
            rw [hw_eq, wires_getD_gate C hRB a b idx.val idx.isLt]
          rcases hlist : g.inputs with _ | ⟨i1, _ | ⟨i2, rest⟩⟩
          · refine ⟨0, ?_⟩
            have hsep : IsSep (val w) := ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun a b => by
              rw [hval_g a b, hlist]; simp⟩
            rw [anchor_of_isSep u v hsep]; simp
          · obtain ⟨c0, c1, haff⟩ := gate_eval_one_affine g.op
            obtain ⟨cf1, hcf1⟩ := ih i1 (hin_lt i1 (by simp [hlist])) (hin_le1 i1 (by simp [hlist]))
            refine ⟨fun k => c1 * cf1 k, ?_⟩
            have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 := by
              ext a b; rw [hval_g a b, hlist]
              exact haff ((C.wires (oneEach a b)).getD i1 false)
            rw [hcomb, anchor_add, anchor_of_isSep u v (isSep_const c0), zero_add,
              anchor_smul, hcf1, Finset.smul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [smul_smul]
          · have hrest : rest = [] := by
              rw [hlist] at hglen
              cases rest with
              | nil => rfl
              | cons _ _ => simp at hglen
            subst hrest
            obtain ⟨c0, c1, c2, hpoly⟩ := gate_eval_two_poly g.op
            have hxor_false : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nonlinear at hnl_false
              rw [hlist] at hnl_false
              simpa using hnl_false
            obtain ⟨cf1, hcf1⟩ := ih i1 (hin_lt i1 (by simp [hlist])) (hin_le1 i1 (by simp [hlist]))
            obtain ⟨cf2, hcf2⟩ := ih i2 (hin_lt i2 (by simp [hlist])) (hin_le1 i2 (by simp [hlist]))
            refine ⟨fun k => c1 * cf1 k + c2 * cf2 k, ?_⟩
            have hcomb : val w = Matrix.of (fun (_ : Fin n) (_ : Fin m) => c0) + c1 • val i1 + c2 • val i2 := by
              ext a b; rw [hval_g a b, hlist]
              have hp := hpoly ((C.wires (oneEach a b)).getD i1 false)
                ((C.wires (oneEach a b)).getD i2 false)
              rw [hxor_false] at hp
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hp
              exact hp
            rw [hcomb, anchor_add, anchor_add, anchor_of_isSep u v (isSep_const c0), zero_add,
              anchor_smul, anchor_smul, hcf1, hcf2, Finset.smul_sum, Finset.smul_sum,
              ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [add_smul, smul_smul, smul_smul]
  have hrep_j : ∀ j : Fin q, ∃ coeff : Fin N → F,
      anchored j = ∑ idx ∈ NL1, coeff idx • Mgate idx := by
    intro j
    obtain ⟨hdep_j, hrepr_j⟩ := htap j
    obtain ⟨coeff, hcoeff⟩ := hdep1_span (tap j) hdep_j
    refine ⟨coeff, ?_⟩
    have hval_j : val (tap j) = entry j := by
      ext a b
      have hr := hrepr_j a b
      change (C.wires (oneEach a b)).getD (tap j) false = G j a b at hr
      simp only [val, entry, b2z, hr]
    change anchor u v (entry j) = _
    rw [← hval_j]
    exact hcoeff
  choose coeff hcoeff using hrep_j
  exact ⟨N, NL1, Mgate, coeff, hNL1_le, hMgate_rank, hcoeff⟩

end FullRefutation



section Pairing

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

lemma pairCoordinates_apply (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (x : K) (i : Fin k) :
    pairCoordinates b bit x i = bit (b i * x) := rfl

noncomputable def pairEquiv (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0) :
    K ≃ₗ[F] (Fin k → F) := by
  letI : FiniteDimensional F K := b.finiteDimensional_of_finite
  have dim : finrank F K = finrank F (Fin k → F) := by
    simp [Module.finrank_eq_card_basis b]
  have hinj : Function.Injective (pairCoordinates b bit) := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : bit.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [pairCoordinates_apply, mul_comm x (b i)] using hi
    apply hbit
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  exact LinearEquiv.ofBijective (pairCoordinates b bit)
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp hinj⟩

noncomputable def pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : K →ₗ[F] K) : Matrix (Fin k) (Fin k) F :=
  fun i j => bit (b i * C (b j))

noncomputable def pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) (hbit : bit ≠ 0)
    (A : Matrix (Fin k) (Fin k) F) : K →ₗ[F] K :=
  (pairEquiv b bit hbit).symm.toLinearMap.comp (Matrix.toLin b (Pi.basisFun F _) A)

lemma pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

lemma pairMatrix_pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (A : Matrix (Fin k) (Fin k) F) :
    pairMatrix b bit (pairMap b bit hbit A) = A := by
  ext i j
  change pairEquiv b bit hbit ((pairEquiv b bit hbit).symm
    (Matrix.toLin b (Pi.basisFun F _) A (b j))) i = A i j
  rw [LinearEquiv.apply_symm_apply, pair_toLin_entry]

lemma pairMatrix_injective (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) : Function.Injective (pairMatrix b bit) := by
  intro C D h
  apply b.ext
  intro j
  apply (pairEquiv b bit hbit).injective
  funext i
  exact congrFun (congrFun h i) j

lemma rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) :
    (pairMatrix b bit C).rank = finrank F (LinearMap.range C) := by
  rw [Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun F _) b]
  have h : Matrix.toLin b (Pi.basisFun F _) (pairMatrix b bit C) =
      (pairEquiv b bit hbit).toLinearMap.comp C := by
    apply b.ext
    intro j
    funext i
    rw [pair_toLin_entry]
    rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq]

end Pairing

section Bridge

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k m : ℕ}

lemma exists_pair_coordinates (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (u : Fin k → F) :
    ∃ a : K, ∀ i, bit (basis i * a) = u i := by
  obtain ⟨a, ha⟩ := (pairEquiv basis bit hbit).surjective u
  exact ⟨a, fun i => congrFun ha i⟩

lemma exists_pair_functional (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (f : K →ₗ[F] F) :
    ∃ a : K, ∀ x, f x = bit (a * x) := by
  obtain ⟨a, ha⟩ := exists_pair_coordinates basis bit hbit (fun i => f (basis i))
  refine ⟨a, ?_⟩
  have h : f = bit.comp (LinearMap.mulLeft F a) := by
    apply basis.ext
    intro i
    simpa [mul_comm] using (ha i).symm
  intro x
  exact DFunLike.congr_fun h x

noncomputable def rankOneEnd (bit : K →ₗ[F] F) (a b : K) : K →ₗ[F] K :=
  (bit.comp (LinearMap.mulLeft F b)).smulRight a

lemma rankOneEnd_apply (bit : K →ₗ[F] F) (a b x : K) :
    rankOneEnd bit a b x = bit (b * x) • a := rfl

lemma pairMatrix_rankOneEnd (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (a b : K) (i j : Fin k) :
    pairMatrix basis bit (rankOneEnd bit a b) i j =
      bit (basis i * a) * bit (b * basis j) := by
  simp only [pairMatrix, rankOneEnd_apply, mul_smul_comm, map_smul]
  exact mul_comm _ _

lemma pairMatrix_sum_rankOneEnd (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (a b : Fin m → K) (i j : Fin k) :
    pairMatrix basis bit (∑ p, rankOneEnd bit (a p) (b p)) i j =
      ∑ p, bit (basis i * a p) * bit (b p * basis j) := by
  simp only [pairMatrix, LinearMap.sum_apply, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact pairMatrix_rankOneEnd basis bit (a p) (b p) i j

lemma exists_field_factorization (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (U : Matrix (Fin k) (Fin m) F) (V : Matrix (Fin m) (Fin k) F) :
    ∃ a b : Fin m → K,
      pairMatrix basis bit (∑ p, rankOneEnd bit (a p) (b p)) = U * V := by
  classical
  have hu : ∀ p, ∃ a : K, ∀ i, bit (basis i * a) = U i p :=
    fun p => exists_pair_coordinates basis bit hbit (fun i => U i p)
  have hv : ∀ p, ∃ b : K, ∀ j, bit (basis j * b) = V p j :=
    fun p => exists_pair_coordinates basis bit hbit (V p)
  choose a ha using hu
  choose b hb using hv
  refine ⟨a, b, ?_⟩
  ext i j
  rw [pairMatrix_sum_rankOneEnd, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ha, mul_comm (b p) (basis j), hb]

lemma rankOne_reciprocal_pair (bit : K →ₗ[F] F) (r a b : K) :
    bit (b * (r * a)) = bit (r * b * a) := by
  congr 1
  ring

lemma pairCoordinates_pairEquiv_symm (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (u : Fin k → F) (i : Fin k) :
    bit (basis i * (pairEquiv basis bit hbit).symm u) = u i := by
  exact congrFun ((pairEquiv basis bit hbit).apply_symm_apply u) i

lemma pairMap_vecMulVec (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (u v : Fin k → F) :
    pairMap basis bit hbit (Matrix.vecMulVec u v) =
      rankOneEnd bit ((pairEquiv basis bit hbit).symm u)
        ((pairEquiv basis bit hbit).symm v) := by
  apply pairMatrix_injective basis bit hbit
  rw [pairMatrix_pairMap]
  ext i j
  rw [pairMatrix_rankOneEnd, pairCoordinates_pairEquiv_symm]
  change u i * v j = u i * bit (_ * basis j)
  rw [mul_comm _ (basis j), pairCoordinates_pairEquiv_symm]

lemma rank_pairMatrix_of_injective (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (C : K →ₗ[F] K) (hC : Function.Injective C) :
    (pairMatrix basis bit C).rank = k := by
  letI : FiniteDimensional F K := basis.finiteDimensional_of_finite
  rw [rank_pairMatrix basis bit hbit C]
  have hs : Function.Surjective C := LinearMap.injective_iff_surjective.mp hC
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_eq_card_basis basis]
  simp

lemma pairMatrix_add (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C D : K →ₗ[F] K) :
    pairMatrix basis bit (C + D) = pairMatrix basis bit C + pairMatrix basis bit D := by
  ext i j
  simp [pairMatrix, mul_add]

lemma pairMatrix_smul (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (c : F) (C : K →ₗ[F] K) :
    pairMatrix basis bit (c • C) = c • pairMatrix basis bit C := by
  ext i j
  simp [pairMatrix, mul_smul_comm]

lemma pairMatrix_sum (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (C : Fin m → K →ₗ[F] K) :
    pairMatrix basis bit (∑ i, C i) = ∑ i, pairMatrix basis bit (C i) := by
  ext i j
  simp [pairMatrix, Finset.mul_sum]

lemma pairMatrix_mulLeft (basis : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (z : K) (i j : Fin k) :
    pairMatrix basis bit (LinearMap.mulLeft F z) i j = bit (z * basis i * basis j) := by
  change bit (basis i * (z * basis j)) = _
  congr 1
  ring

end Bridge



namespace Helper4Algebra

lemma triangular_sum_twice (n : ℕ) :
    2 * (∑ i : Fin n, (i.val + 1)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith

lemma triangular_card (s : ℕ) :
    Fintype.card (Σ i : Fin (2*s), Fin (i.val + 1)) = s*(2*s+1) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h := triangular_sum_twice (2*s)
  nlinarith

lemma exists_strict_upper
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s : ℕ)
    (entry : Fin (2*s) → Fin (2*s) → V →ₗ[K] K)
    (hdim : s*(2*s+1) < Module.finrank K V) :
    ∃ w : V, w ≠ 0 ∧ ∀ i j : Fin (2*s), j ≤ i → entry i j w = 0 := by
  let L : V →ₗ[K] ((Σ i : Fin (2*s), Fin (i.val + 1)) → K) :=
    LinearMap.pi fun p => entry p.1
      ⟨p.2.val, lt_of_lt_of_le p.2.isLt (Nat.succ_le_iff.mpr p.1.isLt)⟩
  have hdim' : Module.finrank K ((Σ i : Fin (2*s), Fin (i.val + 1)) → K) <
      Module.finrank K V := by
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, triangular_card] using hdim
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim'
  obtain ⟨w, hw, hn⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  refine ⟨w, hn, ?_⟩
  intro i j hji
  have hz : L w = 0 := hw
  exact congrFun hz ⟨i, ⟨j.val, Nat.lt_succ_of_le hji⟩⟩

lemma masked_det_eq_one
    (K : Type*) [Field K] (r : ℕ) (M : Matrix (Fin r) (Fin r) K)
    (hM : ∀ i j, j ≤ i → M i j = 0) (mask : Fin r → K) :
    (1 + (Matrix.of fun i j => M i j * mask j) : Matrix (Fin r) (Fin r) K).det = 1 := by
  have ht : (1 + (Matrix.of fun i j => M i j * mask j) :
      Matrix (Fin r) (Fin r) K).IsUpperTriangular := by
    intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    simp [hM i j (le_of_lt hji), hne]
  rw [Matrix.det_of_isUpperTriangular ht]
  simp [hM]

lemma exists_strict_upper_of_le
    (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (r s : ℕ) (hrs : r ≤ 2*s)
    (entry : Fin r → Fin r → V →ₗ[K] K)
    (hdim : s*(2*s+1) < Module.finrank K V) :
    ∃ w : V, w ≠ 0 ∧ ∀ i j : Fin r, j ≤ i → entry i j w = 0 := by
  let L : V →ₗ[K] ((Σ i : Fin r, Fin (i.val + 1)) → K) :=
    LinearMap.pi fun p => entry p.1
      ⟨p.2.val, lt_of_lt_of_le p.2.isLt (Nat.succ_le_iff.mpr p.1.isLt)⟩
  have hcard : Fintype.card (Σ i : Fin r, Fin (i.val + 1)) ≤ s*(2*s+1) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have hsum := triangular_sum_twice r
    have hprod := Nat.mul_le_mul hrs (Nat.add_le_add_right hrs 1)
    nlinarith
  have hdim' : Module.finrank K ((Σ i : Fin r, Fin (i.val + 1)) → K) <
      Module.finrank K V := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact lt_of_le_of_lt hcard hdim
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim'
  obtain ⟨w, hw, hn⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  refine ⟨w, hn, ?_⟩
  intro i j hji
  have hz : L w = 0 := hw
  exact congrFun hz ⟨i, ⟨j.val, Nat.lt_succ_of_le hji⟩⟩

lemma odd_half_strict (k : ℕ) (hk : k % 2 = 1) : 2 * (k / 2) < k := by
  omega

end Helper4Algebra


namespace FullAlgebra

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

lemma triangular_rankOne_injective (m : ℕ) (bit : K →ₗ[F] F)
    (a b : Fin m → K) (r : K) (hr : r ≠ 0)
    (htri : ∀ i j : Fin m, j ≤ i → bit (b i * (r * a j)) = 0)
    (d : Fin m → F) :
    Function.Injective
      (LinearMap.mulLeft F r⁻¹ + ∑ j, d j • rankOneEnd bit (a j) (b j)) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : r⁻¹*x + ∑ j, (d j * bit (b j*x)) • a j = 0 := by
    simpa only [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.mulLeft_apply,
      LinearMap.sum_apply, LinearMap.smul_apply, rankOneEnd_apply, smul_smul] using hx
  let c : Fin m → F := fun i => bit (b i * x)
  let B : Matrix (Fin m) (Fin m) F := fun i j => bit (b i * (r * a j))
  let A : Matrix (Fin m) (Fin m) F := 1 + Matrix.of (fun i j => B i j * d j)
  have hlin : ∀ i, c i + ∑ j, (B i j * d j) * c j = 0 := by
    intro i
    have hi := congrArg (fun y : K => bit (b i * (r * y))) hx'
    simp only [mul_add, Finset.mul_sum, mul_smul_comm, map_add, map_sum, map_smul,
      mul_zero, map_zero] at hi
    have hfirst : bit (b i * (r * (r⁻¹ * x))) = c i := by
      simp [c, ← mul_assoc, hr]
    rw [hfirst] at hi
    convert hi using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [B, c]
    ring
  have hAc : A.mulVec c = 0 := by
    ext i
    change ((1 : Matrix (Fin m) (Fin m) F) + Matrix.of (fun i j => B i j * d j)).mulVec c i = 0
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    exact hlin i
  have hc : c = 0 := by
    by_contra hne
    have hz : A.det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hne, hAc⟩
    have ho : A.det = 1 := Helper4Algebra.masked_det_eq_one F m B htri d
    exact one_ne_zero (ho.symm.trans hz)
  have hbitx : ∀ j, bit (b j*x) = 0 := fun j => congrFun hc j
  simp only [hbitx, mul_zero, zero_smul, Finset.sum_const_zero, add_zero] at hx'
  exact (mul_eq_zero.mp hx').resolve_left (inv_ne_zero hr)

lemma exists_full_rank_perturbation {k : ℕ} (basis : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (hbit : bit ≠ 0) (m s : ℕ) (hms : m ≤ 2*s)
    (hdim : s*(2*s+1) < k) (u v : Fin m → Fin k → F) :
    ∃ z : K, z ≠ 0 ∧ ∀ d : Fin m → F,
      (pairMatrix basis bit (LinearMap.mulLeft F z) +
        ∑ p, d p • Matrix.vecMulVec (u p) (v p)).rank = k := by
  classical
  letI : FiniteDimensional F K := basis.finiteDimensional_of_finite
  let a : Fin m → K := fun p => (pairEquiv basis bit hbit).symm (u p)
  let b : Fin m → K := fun p => (pairEquiv basis bit hbit).symm (v p)
  let entry : Fin m → Fin m → K →ₗ[F] F :=
    fun i j => bit.comp (LinearMap.mulLeft F (b i * a j))
  have hd : s*(2*s+1) < finrank F K := by
    simpa [Module.finrank_eq_card_basis basis] using hdim
  obtain ⟨r, hr, htri⟩ := Helper4Algebra.exists_strict_upper_of_le F K m s hms entry hd
  have ht : ∀ i j, j ≤ i → bit (b i * (r * a j)) = 0 := by
    intro i j hij
    simpa [entry, mul_assoc, mul_comm, mul_left_comm] using htri i j hij
  have hvec : ∀ p, pairMatrix basis bit (rankOneEnd bit (a p) (b p)) =
      Matrix.vecMulVec (u p) (v p) := by
    intro p
    ext i j
    rw [pairMatrix_rankOneEnd]
    dsimp [a, b]
    rw [pairCoordinates_pairEquiv_symm, mul_comm _ (basis j),
      pairCoordinates_pairEquiv_symm]
    rfl
  refine ⟨r⁻¹, inv_ne_zero hr, ?_⟩
  intro d
  have hinj := triangular_rankOne_injective m bit a b r hr ht d
  have hfull := rank_pairMatrix_of_injective basis bit hbit _ hinj
  have heq : pairMatrix basis bit
      (LinearMap.mulLeft F r⁻¹ + ∑ p, d p • rankOneEnd bit (a p) (b p)) =
      pairMatrix basis bit (LinearMap.mulLeft F r⁻¹) +
        ∑ p, d p • Matrix.vecMulVec (u p) (v p) := by
    rw [pairMatrix_add, pairMatrix_sum]
    simp only [pairMatrix_smul, hvec]
  rw [heq] at hfull
  exact hfull

end FullAlgebra

namespace LowRankFamily

open Module

lemma factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl

lemma exists_full_rank_lowrank_family {K : Type*} [Field K] [Algebra (ZMod 2) K]
    {k : ℕ} (basis : Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (s : ℕ) (hdim : s*(2*s+1) < k)
    (ι : Type*) [Fintype ι] (hcard : Fintype.card ι ≤ s)
    (M : ι → Matrix (Fin k) (Fin k) (ZMod 2)) (hM : ∀ i, (M i).rank ≤ 2) :
    ∃ z : K, z ≠ 0 ∧ ∀ d : ι → ZMod 2,
      (pairMatrix basis bit (LinearMap.mulLeft (ZMod 2) z) +
        ∑ i, d i • M i).rank = k := by
  classical
  have hf : ∀ i, ∃ (u v : Fin 2 → Fin k → ZMod 2),
      ∀ a b, M i a b = ∑ t : Fin 2, u t a * v t b :=
    fun i => factor_of_rank_le (M i) (hM i)
  choose u v hf using hf
  have hfac : ∀ i, M i = ∑ t : Fin 2, Matrix.vecMulVec (u i t) (v i t) := by
    intro i
    ext a b
    simpa only [Matrix.sum_apply, Finset.sum_apply, Matrix.vecMulVec_apply] using hf i a b
  let m := Fintype.card (ι × Fin 2)
  let e : Fin m ≃ (ι × Fin 2) := (Fintype.equivFin (ι × Fin 2)).symm
  let U : Fin m → Fin k → ZMod 2 := fun p => u (e p).1 (e p).2
  let V : Fin m → Fin k → ZMod 2 := fun p => v (e p).1 (e p).2
  have hm : m ≤ 2*s := by
    dsimp [m]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨z, hz, hr⟩ := FullAlgebra.exists_full_rank_perturbation basis bit hbit m s hm hdim U V
  refine ⟨z, hz, ?_⟩
  intro d
  have heq : (∑ p : Fin m, d (e p).1 • Matrix.vecMulVec (U p) (V p)) =
      ∑ i, d i • M i := by
    calc
      _ = ∑ p : ι × Fin 2, d p.1 • Matrix.vecMulVec (u p.1 p.2) (v p.1 p.2) :=
        e.sum_comp (fun p : ι × Fin 2 => d p.1 • Matrix.vecMulVec (u p.1 p.2) (v p.1 p.2))
      _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.smul_sum, ← hfac]
  have hh := hr (fun p => d (e p).1)
  rw [heq] at hh
  exact hh

end LowRankFamily

namespace FullRefutation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private def fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩

private def reducedAnchor {k : ℕ} (G : Fin (k+1) → Fin (k+1) → Bool) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  fun i j => b2z (G i.succ j.succ) + b2z (G i.succ 0) +
    b2z (G 0 j.succ) + b2z (G 0 0)

private lemma common_reduced {k q : ℕ} (G : Fin q → Fin (k+1) → Fin (k+1) → Bool)
    (t : ℕ) (hf : fits (k+1) (k+1) q G t) :
    ∃ N : ℕ, ∃ J : Finset (Fin N),
      ∃ M : Fin N → Matrix (Fin k) (Fin k) (ZMod 2),
      ∃ coeff : Fin q → Fin N → ZMod 2, J.card ≤ t ∧
        (∀ i ∈ J, (M i).rank ≤ 2) ∧
        ∀ j : Fin q, reducedAnchor (G j) = ∑ i ∈ J, coeff j i • M i := by
  obtain ⟨C, tap, hrb, hfan, hcnt, htap⟩ := hf
  obtain ⟨N,J,M,c,hJ,hM,hc⟩ := forward_aux G 0 0 t C tap hrb hfan hcnt htap
  refine ⟨N,J,fun i => (M i).submatrix Fin.succ Fin.succ,c,hJ,?_,?_⟩
  · intro i hi
    exact (Matrix.rank_submatrix_le (M i) Fin.succ Fin.succ).trans (hM i hi)
  · intro j
    ext a b
    have hh := congrFun (congrFun (hc j) a.succ) b.succ
    simpa [reducedAnchor, b2z, Matrix.sum_apply, Finset.sum_apply,
      Matrix.smul_apply, Matrix.submatrix_apply] using hh

private lemma fits_reduced_rank {k q : ℕ} (G : Fin q → Fin (k+1) → Fin (k+1) → Bool)
    (t : ℕ) (hf : fits (k+1) (k+1) q G t) (j : Fin q) :
    (reducedAnchor (G j)).rank ≤ 2*t := by
  classical
  obtain ⟨N,J,M,c,hJ,hM,hc⟩ := common_reduced G t hf
  rw [hc j]
  calc
    _ ≤ ∑ i ∈ J, (c j i • M i).rank := matrix_rank_sum_le J _
    _ ≤ ∑ _i ∈ J, 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rcases zmod2_cases (c j i) with h | h
      · simp [h]
      · simpa [h] using hM i hi
    _ = 2*J.card := by simp [Nat.mul_comm]
    _ ≤ 2*t := Nat.mul_le_mul_left 2 hJ

private lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private lemma b2z_parity (n : ℕ) : b2z ((n % 2) == 1) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h, b2z]

private lemma b2z_mask {q : ℕ} (S : Finset (Fin q)) (f : Fin q → Bool) :
    b2z (((S.filter (fun i => f i)).card % 2) == 1) = ∑ i ∈ S, b2z (f i) := by
  rw [b2z_parity]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, b2z]

private def maskTable {k q : ℕ} (G : Fin q → Fin (k+1) → Fin (k+1) → Bool)
    (S : Finset (Fin q)) (x y : Fin (k+1)) : Bool :=
  ((S.filter (fun i => G i x y)).card % 2) == 1

private lemma reducedAnchor_xor {k : ℕ} (A B : Fin (k+1) → Fin (k+1) → Bool) :
    reducedAnchor (fun x y => xor (A x y) (B x y)) = reducedAnchor A + reducedAnchor B := by
  ext i j
  simp only [reducedAnchor, b2z_xor, Matrix.add_apply]
  ring

private lemma reducedAnchor_mask {k q : ℕ}
    (G : Fin q → Fin (k+1) → Fin (k+1) → Bool) (S : Finset (Fin q)) :
    reducedAnchor (maskTable G S) = ∑ i ∈ S, reducedAnchor (G i) := by
  ext a b
  simp only [reducedAnchor, maskTable, b2z_mask, Matrix.sum_apply, Finset.sum_apply]
  simp only [Finset.sum_add_distrib]

private lemma b2z_ne_zero (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a
  · change b2z (decide ((0 : ZMod 2) ≠ 0)) = 0
    decide
  · change b2z (decide ((1 : ZMod 2) ≠ 0)) = 1
    decide

private noncomputable def fieldTable {K : Type*} [Field K] [Algebra (ZMod 2) K] {k : ℕ}
    (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (z : K) (x y : Fin (k+1)) : Bool :=
  decide (bit (z * Fin.cases 0 basis x * Fin.cases 0 basis y) ≠ 0)

private lemma reducedAnchor_field {K : Type*} [Field K] [Algebra (ZMod 2) K] {k : ℕ}
    (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (z : K) :
    reducedAnchor (fieldTable basis bit z) = pairMatrix basis bit (LinearMap.mulLeft (ZMod 2) z) := by
  ext i j
  simp only [reducedAnchor, fieldTable, b2z_ne_zero, Fin.cases_succ, Fin.cases_zero,
    mul_zero, zero_mul, map_zero, add_zero, pairMatrix_mulLeft]
  exact b2z_ne_zero _

private theorem no_cover {K : Type*} [Field K] [Algebra (ZMod 2) K] {k q : ℕ}
    (basis : Module.Basis (Fin k) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2)
    (hbit : bit ≠ 0) (s : ℕ) (hodd : k % 2 = 1) (hdim : s*(2*s+1) < k)
    (T : Fin q → Fin (k+1) → Fin (k+1) → Bool)
    (hprep : fits (k+1) (k+1) q T s)
    (hserve : ∀ z : K, z ≠ 0 → ∃ S : Finset (Fin q),
      fits (k+1) (k+1) 1 (fun _ x y => xor (fieldTable basis bit z x y) (maskTable T S x y)) (k/2)) :
    False := by
  classical
  obtain ⟨N,J,M,c,hJ,hM,hc⟩ := common_reduced T s hprep
  have hcard : Fintype.card J ≤ s := by simpa using hJ
  obtain ⟨z,hz,hfull⟩ := LowRankFamily.exists_full_rank_lowrank_family
    basis bit hbit s hdim J hcard (fun i => M i.val) (fun i => hM i.val i.property)
  obtain ⟨S,hcorr⟩ := hserve z hz
  let d : J → ZMod 2 := fun i => ∑ j ∈ S, c j i.val
  have heq : reducedAnchor (fun x y => xor (fieldTable basis bit z x y) (maskTable T S x y)) =
      pairMatrix basis bit (LinearMap.mulLeft (ZMod 2) z) + ∑ i : J, d i • M i.val := by
    rw [reducedAnchor_xor, reducedAnchor_field, reducedAnchor_mask]
    congr 1
    simp_rw [hc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    exact (Finset.sum_attach J (fun i => (∑ j ∈ S, c j i) • M i)).symm
  have hr := fits_reduced_rank
    (fun (_ : Fin 1) x y => xor (fieldTable basis bit z x y) (maskTable T S x y)) (k/2) hcorr 0
  rw [heq, hfull d] at hr
  exact (Nat.not_le_of_gt (Helper4Algebra.odd_half_strict k hodd)) hr

end FullRefutation

end PEqualNP.Outside.L_meta_26032_aux

theorem PEqualNP.Outside.L_meta_26032 : ¬ (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∃ (k s g : ℕ), 3 ≤ s ∧ k % 2 = 1 ∧ s*(2*s+1) < k ∧
  ∃ (basis : Module.Basis (Fin k) F (GaloisField 2 k))
    (bit : GaloisField 2 k →ₗ[F] F), bit ≠ 0 ∧
  let n := k+1
  let point : Fin n → GaloisField 2 k := Fin.cases 0 basis
  let mult := fun (z : GaloisField 2 k) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : GaloisField 2 k) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)

  ∃ T : Fin g → Fin n → Fin n → Bool, fits n n g T s ∧
    ∀ z : GaloisField 2 k, z ≠ 0 →
      ∃ S : Finset (Fin g), fits n n 1 (fun _ => residual T S z) (k/2)
) := by
  intro h
  rcases h with ⟨k,s,g,hs,hodd,hdim,basis,bit,hbit,T,hprep,hserve⟩
  exact PEqualNP.Outside.L_meta_26032_aux.FullRefutation.no_cover basis bit hbit s hodd hdim T hprep hserve
