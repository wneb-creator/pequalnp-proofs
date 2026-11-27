import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26032_aux

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

private theorem factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
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

theorem common_factors {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ)
    (C : Circuit) (tap : Fin q → ℕ)
    (hRB : ReadsBack (n + m) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nonlinear ≤ t)
    (htap : ∀ j : Fin q, (depths (n + m) C).getD (tap j) 0 ≤ 1 ∧ Represents (G j) ⟨C.gates, tap j⟩) :
    ∃ r, r ≤ 2 * t ∧ ∃ (U : Fin r → Fin n → ZMod 2) (V : Fin r → Fin m → ZMod 2)
      (c : Fin q → Fin r → ZMod 2), ∀ j,
      anchor u v (fun x y => b2z (G j x y)) =
        ∑ i : Fin r, c j i • Matrix.vecMulVec (U i) (V i) := by
  classical
  let F := ZMod 2
  let Mat := Matrix (Fin n) (Fin m) F
  let entry := fun j a b => b2z (G j a b)
  let anchored : Fin q → Mat := fun j => anchor u v (entry j)
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
  have hfac : ∀ idx : ↥NL1, ∃ (rowVec : Fin 2 → Fin n → F) (colVec : Fin 2 → Fin m → F),
      Mgate idx = ∑ h : Fin 2, Matrix.vecMulVec (rowVec h) (colVec h) := by
    intro idx
    obtain ⟨rowVec, colVec, he⟩ := factor_of_rank_le (Mgate idx) (hMgate_rank idx idx.property)
    refine ⟨rowVec, colVec, ?_⟩
    ext a b
    simpa only [Matrix.sum_apply, Finset.sum_apply, Matrix.vecMulVec_apply] using he a b
  choose rowVec colVec hfac using hfac
  let I := ↥NL1 × Fin 2
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, ?_, (fun i => rowVec (e i).1 (e i).2),
    (fun i => colVec (e i).1 (e i).2), (fun j i => coeff j (e i).1), ?_⟩
  · simp only [I, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    omega
  · intro j
    change anchored j = ∑ i : Fin (Fintype.card I),
      coeff j (e i).1 • Matrix.vecMulVec (rowVec (e i).1 (e i).2) (colVec (e i).1 (e i).2)
    rw [hcoeff j]
    rw [Equiv.sum_comp e (fun i : I => coeff j i.1 •
      Matrix.vecMulVec (rowVec i.1 i.2) (colVec i.1 i.2))]
    calc
      ∑ idx ∈ NL1, coeff j idx • Mgate idx =
          ∑ idx : ↥NL1, coeff j idx • Mgate idx := (Finset.sum_coe_sort NL1 _).symm
      _ = ∑ idx : ↥NL1, ∑ h : Fin 2,
          coeff j idx • Matrix.vecMulVec (rowVec idx h) (colVec idx h) := by
        apply Finset.sum_congr rfl
        intro idx _
        rw [hfac idx, Finset.smul_sum]
      _ = ∑ i : I, coeff j i.1 • Matrix.vecMulVec (rowVec i.1 i.2) (colVec i.1 i.2) :=
        (Fintype.sum_prod_type (fun i : I => coeff j i.1 •
          Matrix.vecMulVec (rowVec i.1 i.2) (colVec i.1 i.2))).symm




open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

noncomputable def pairCoordinates (b : Basis (Fin k) F K) (bit : K →ₗ[F] F) :
    K →ₗ[F] (Fin k → F) :=
  LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (b i))

theorem pairCoordinates_apply (b : Basis (Fin k) F K)
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

theorem pair_toLin_entry (b : Basis (Fin k) F K) (A : Matrix (Fin k) (Fin k) F)
    (i j : Fin k) : Matrix.toLin b (Pi.basisFun F _) A (b j) i = A i j := by
  rw [Matrix.toLin_self]
  simp [Pi.single_apply, mul_ite]

theorem pairMatrix_pairMap (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (A : Matrix (Fin k) (Fin k) F) :
    pairMatrix b bit (pairMap b bit hbit A) = A := by
  ext i j
  change pairEquiv b bit hbit ((pairEquiv b bit hbit).symm
    (Matrix.toLin b (Pi.basisFun F _) A (b j))) i = A i j
  rw [LinearEquiv.apply_symm_apply, pair_toLin_entry]

theorem pairMatrix_injective (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) : Function.Injective (pairMatrix b bit) := by
  intro C D h
  apply b.ext
  intro j
  apply (pairEquiv b bit hbit).injective
  funext i
  exact congrFun (congrFun h i) j

theorem rank_pairMatrix (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
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


lemma triangle_sum_fixed_zero
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {r : ℕ} (u : Fin r → V) (v : Fin r → V →ₗ[F] F)
    (c : Fin r → F)
    (tri : ∀ i j : Fin r, j ≤ i → v i (u j) = 0)
    (x : V) (hx : x = ∑ j : Fin r, (c j * v j x) • u j) : x = 0 := by
  have vanishes : ∀ n : ℕ, ∀ i : Fin r, r - i.val = n → v i x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hi
      rw [hx, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul]
      by_cases hji : j ≤ i
      · rw [tri i j hji, smul_zero]
      · have hlt : r - j.val < n := by
          have hj : i.val < j.val := by exact lt_of_not_ge hji
          have hir := i.isLt
          have hjr := j.isLt
          omega
        rw [ih (r - j.val) hlt j rfl, mul_zero, zero_smul]
  rw [hx]
  apply Finset.sum_eq_zero
  intro j _
  rw [vanishes (r - j.val) j rfl, mul_zero, zero_smul]

lemma triangle_field_kernel
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {r : ℕ} (u v : Fin r → K) (bit : K →ₗ[F] F)
    (c : Fin r → F) (w z : K) (hwz : w * z = 1)
    (tri : ∀ i j : Fin r, j ≤ i → bit (v i * w * u j) = 0)
    (x : K) (hx : z * x + ∑ j : Fin r, (c j * bit (v j * x)) • u j = 0) :
    x = 0 := by
  let forms : Fin r → K →ₗ[F] F := fun i => bit.comp (LinearMap.mulLeft F (v i))
  apply triangle_sum_fixed_zero (fun j => w * u j) forms (fun j => -c j) ?_ x ?_
  · intro i j hji
    simpa [forms, mul_assoc] using tri i j hji
  · have he : z * x = -(∑ j : Fin r, (c j * bit (v j * x)) • u j) :=
      eq_neg_of_add_eq_zero_left hx
    calc
      x = w * (z * x) := by rw [← mul_assoc, hwz, one_mul]
      _ = -(w * ∑ j : Fin r, (c j * bit (v j * x)) • u j) := by rw [he, mul_neg]
      _ = ∑ j : Fin r, (-c j * forms j x) • (w * u j) := by
        simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp [forms, Algebra.smul_def]
        ring

lemma triangle_field_kernel_forms
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    {r : ℕ} (u : Fin r → K) (v : Fin r → K →ₗ[F] F)
    (c : Fin r → F) (w z : K) (hwz : w * z = 1)
    (tri : ∀ i j : Fin r, j ≤ i → v i (w * u j) = 0)
    (x : K) (hx : z * x + ∑ j : Fin r, (c j * v j x) • u j = 0) :
    x = 0 := by
  apply triangle_sum_fixed_zero (fun j => w * u j) v (fun j => -c j) tri x
  have he : z * x = -(∑ j : Fin r, (c j * v j x) • u j) :=
    eq_neg_of_add_eq_zero_left hx
  calc
    x = w * (z * x) := by rw [← mul_assoc, hwz, one_mul]
    _ = -(w * ∑ j : Fin r, (c j * v j x) • u j) := by rw [he, mul_neg]
    _ = ∑ j : Fin r, (-c j * v j x) • (w * u j) := by
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Algebra.smul_def, map_mul, map_neg]
      ring

lemma triangle_indices_card (r : ℕ) :
    2 * Fintype.card (Σ i : Fin r, Fin (i.val + 1)) = r * (r + 1) := by
  simp only [Fintype.card_sigma, Fintype.card_fin]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith

lemma exists_triangle_kernel (b : Basis (Fin k) F K) {r : ℕ}
    (u : Fin r → K) (v : Fin r → K →ₗ[F] F)
    (hdim : r * (r + 1) < 2 * k) :
    ∃ w : K, w ≠ 0 ∧ ∀ i j : Fin r, j ≤ i → v i (w * u j) = 0 := by
  classical
  let I := Σ i : Fin r, Fin (i.val + 1)
  let f : K →ₗ[F] (I → F) := LinearMap.pi fun p =>
    (v p.1).comp (LinearMap.mulRight F (u ⟨p.2.val, by omega⟩))
  have hd : Fintype.card I < k := by
    have he := triangle_indices_card r
    change 2 * Fintype.card I = r * (r + 1) at he
    omega
  have hnot : ¬ Function.Injective f := by
    intro hi
    have hle := f.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_eq_card_basis b, Fintype.card_fin,
      Module.finrank_fintype_fun_eq_card] at hle
    exact (not_le_of_gt hd) hle
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    exact hnot (LinearMap.ker_eq_bot.mp h)
  obtain ⟨w, hw, hn⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  refine ⟨w, hn, ?_⟩
  intro i j hji
  have he := congrFun (LinearMap.mem_ker.mp hw) (⟨i, ⟨j.val, by omega⟩⟩ : I)
  exact he

noncomputable def rankOneForm (b : Basis (Fin k) F K) (v : Fin k → F) : K →ₗ[F] F :=
  ∑ j : Fin k, v j • b.coord j

lemma rankOneForm_basis (b : Basis (Fin k) F K) (v : Fin k → F) (j : Fin k) :
    rankOneForm b v (b j) = v j := by
  classical
  simp [rankOneForm, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

lemma pairMatrix_add (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (A B : K →ₗ[F] K) :
    pairMatrix b bit (A + B) = pairMatrix b bit A + pairMatrix b bit B := by
  ext i j
  simp [pairMatrix, mul_add]

lemma pairMatrix_smul (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (c : F) (A : K →ₗ[F] K) :
    pairMatrix b bit (c • A) = c • pairMatrix b bit A := by
  ext i j
  simp [pairMatrix]

lemma pairMatrix_sum {I : Type*} [Fintype I] (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (A : I → K →ₗ[F] K) :
    pairMatrix b bit (∑ i, A i) = ∑ i, pairMatrix b bit (A i) := by
  ext i j
  simp [pairMatrix, Finset.mul_sum, map_sum]

lemma pairMatrix_rankOne (b : Basis (Fin k) F K) (bit : K →ₗ[F] F)
    (hbit : bit ≠ 0) (u v : Fin k → F) :
    pairMatrix b bit ((rankOneForm b v).smulRight ((pairEquiv b bit hbit).symm u)) =
      Matrix.vecMulVec u v := by
  ext i j
  change bit (b i * (rankOneForm b v (b j) • (pairEquiv b bit hbit).symm u)) = _
  rw [rankOneForm_basis, mul_smul_comm, map_smul]
  have hu : bit (b i * (pairEquiv b bit hbit).symm u) = u i :=
    congrFun ((pairEquiv b bit hbit).apply_symm_apply u) i
  rw [hu]
  simp [Matrix.vecMulVec, mul_comm]

lemma field_rank_obstruction (b : Basis (Fin k) F K)
    (bit : K →ₗ[F] F) (hbit : bit ≠ 0) {r : ℕ}
    (U V : Fin r → Fin k → F)
    (hdim : r * (r + 1) < 2 * k) :
    ∃ z : K, z ≠ 0 ∧ ∀ c : Fin r → F,
      (Matrix.of (fun i j => bit (z * b i * b j)) +
        ∑ h : Fin r, c h • Matrix.vecMulVec (U h) (V h)).rank = k := by
  classical
  let : FiniteDimensional F K := b.finiteDimensional_of_finite
  let u : Fin r → K := fun h => (pairEquiv b bit hbit).symm (U h)
  let v : Fin r → K →ₗ[F] F := fun h => rankOneForm b (V h)
  obtain ⟨w, hw, tri⟩ := exists_triangle_kernel b u v hdim
  refine ⟨w⁻¹, inv_ne_zero hw, ?_⟩
  intro c
  let C : K →ₗ[F] K := LinearMap.mulLeft F w⁻¹ +
    ∑ h : Fin r, c h • (v h).smulRight (u h)
  have hC_apply (x : K) : C x = w⁻¹ * x +
      ∑ h : Fin r, (c h * v h x) • u h := by
    simp [C, smul_smul]
  have hC : Function.Injective C := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [hC_apply] at hx
    exact triangle_field_kernel_forms u v c w w⁻¹ (mul_inv_cancel₀ hw) tri x hx
  have hmatrix : (Matrix.of (fun i j => bit (w⁻¹ * b i * b j)) +
      ∑ h : Fin r, c h • Matrix.vecMulVec (U h) (V h)) = pairMatrix b bit C := by
    dsimp only [C]
    rw [pairMatrix_add, pairMatrix_sum]
    congr 1
    · ext i j
      change bit (w⁻¹ * b i * b j) = bit (b i * (w⁻¹ * b j))
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro h _
      rw [pairMatrix_smul, pairMatrix_rankOne]
  rw [hmatrix, rank_pairMatrix b bit hbit C, LinearMap.finrank_range_of_inj hC]
  simp [Module.finrank_eq_card_basis b]


lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_parity_nat (n : ℕ) : b2z (n % 2 == 1) = (n : ZMod 2) := by
  apply Fin.ext
  change (b2z (n % 2 == 1)).val = (n : ZMod 2).val
  rw [ZMod.val_natCast]
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [b2z, h]; decide

lemma b2z_parity {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → Bool) :
    b2z (((S.filter (fun i => f i)).card % 2) == 1) = ∑ i ∈ S, b2z (f i) := by
  rw [b2z_parity_nat]
  simp only [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases f i <;> simp [b2z]

lemma b2z_decide_ne_zero (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  revert a
  decide



private def Fits (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ),
    ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates, tap j⟩

private lemma fits_rank_bound {n m : ℕ} (G : Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m) (t : ℕ) (hfits : Fits n m 1 (fun _ => G) t) :
    (anchor u v (fun x y => b2z (G x y))).rank ≤ 2*t := by
  classical
  obtain ⟨C, tap, hRB, hfan, hcnt, htap⟩ := hfits
  obtain ⟨r, hr, U, V, c, hfac⟩ := common_factors (fun _ : Fin 1 => G) u v t C tap
    hRB hfan hcnt htap
  rw [hfac 0]
  calc
    (∑ i : Fin r, c 0 i • Matrix.vecMulVec (U i) (V i)).rank
        ≤ ∑ i : Fin r, (c 0 i • Matrix.vecMulVec (U i) (V i)).rank :=
          matrix_rank_sum_le Finset.univ _
    _ ≤ ∑ _i : Fin r, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      have he : c 0 i • Matrix.vecMulVec (U i) (V i) =
          Matrix.vecMulVec (fun a => c 0 i * U i a) (V i) := by
        ext a b
        simp [Matrix.vecMulVec_apply, mul_assoc]
      rw [he]
      exact Matrix.rank_vecMulVec_le _ _
    _ = r := by simp
    _ ≤ 2*t := hr

private lemma anchor_sum {ι : Type} [DecidableEq ι] {n m : ℕ}
    (u : Fin n) (v : Fin m) (S : Finset ι)
    (A : ι → Matrix (Fin n) (Fin m) (ZMod 2)) :
    anchor u v (∑ i ∈ S, A i) = ∑ i ∈ S, anchor u v (A i) := by
  induction S using Finset.induction_on with
  | empty => simp [anchor_zero]
  | @insert i S hi ih => rw [Finset.sum_insert hi, anchor_add, ih, Finset.sum_insert hi]

private lemma residual_anchor {k g : ℕ}
    (basis : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k))
    (bit : GaloisField 2 k →ₗ[ZMod 2] ZMod 2)
    (T : Fin g → Fin (k+1) → Fin (k+1) → Bool) (S : Finset (Fin g))
    (z : GaloisField 2 k) :
    (anchor 0 0 (fun x y => b2z (xor
      (decide (bit (z * Fin.cases 0 basis x * Fin.cases 0 basis y) ≠ 0))
      (((S.filter (fun i => T i x y)).card % 2) == 1)))).submatrix Fin.succ Fin.succ =
      (Matrix.of fun i j => bit (z * basis i * basis j)) +
      (∑ a ∈ S, anchor 0 0 (fun x y => b2z (T a x y))).submatrix Fin.succ Fin.succ := by
  ext i j
  simp only [anchor, Matrix.submatrix_apply, Matrix.of_apply, Matrix.add_apply,
    Matrix.sum_apply, b2z_xor, b2z_decide_ne_zero, b2z_parity,
    Fin.cases_zero, Fin.cases_succ, zero_mul, mul_zero, map_zero,
    zero_add, Finset.sum_add_distrib]
  ring


private lemma submatrix_factors {k g r : ℕ}
    (T : Fin g → Fin (k+1) → Fin (k+1) → Bool)
    (U V : Fin r → Fin (k+1) → ZMod 2) (c : Fin g → Fin r → ZMod 2)
    (hfac : ∀ j, anchor 0 0 (fun x y => b2z (T j x y)) =
      ∑ i : Fin r, c j i • Matrix.vecMulVec (U i) (V i)) (S : Finset (Fin g)) :
    (∑ a ∈ S, anchor 0 0 (fun x y => b2z (T a x y))).submatrix Fin.succ Fin.succ =
      ∑ i : Fin r, (∑ a ∈ S, c a i) •
        Matrix.vecMulVec (fun j => U i j.succ) (fun j => V i j.succ) := by
  simp_rw [hfac]
  rw [Finset.sum_comm]
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]



private lemma impossible (k s g : ℕ) (hodd : k % 2 = 1)
    (hlarge : s*(2*s+1) < k)
    (basis : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k))
    (bit : GaloisField 2 k →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (T : Fin g → Fin (k+1) → Fin (k+1) → Bool)
    (hT : Fits (k+1) (k+1) g T s)
    (hcover : ∀ z : GaloisField 2 k, z ≠ 0 →
      ∃ S : Finset (Fin g), Fits (k+1) (k+1) 1 (fun _ x y => xor
        (decide (bit (z * Fin.cases 0 basis x * Fin.cases 0 basis y) ≠ 0))
        (((S.filter (fun i => T i x y)).card % 2) == 1)) (k/2)) : False := by
  classical
  obtain ⟨C, tap, hRB, hfan, hcnt, htap⟩ := hT
  obtain ⟨r, hr, U, V, c, hfac⟩ := common_factors T 0 0 s C tap hRB hfan hcnt htap
  have hdim : r*(r+1) < 2*k := by
    have hp := Nat.mul_le_mul hr (Nat.add_le_add_right hr 1)
    nlinarith
  obtain ⟨z, hz, hfull⟩ := field_rank_obstruction basis bit hbit
    (fun i j => U i j.succ) (fun i j => V i j.succ) hdim
  obtain ⟨S, hS⟩ := hcover z hz
  have hbound := fits_rank_bound _ 0 0 (k/2) hS
  have hsub := Matrix.rank_submatrix_le
    (anchor 0 0 (fun x y => b2z (xor
      (decide (bit (z * Fin.cases 0 basis x * Fin.cases 0 basis y) ≠ 0))
      (((S.filter (fun i => T i x y)).card % 2) == 1)))) Fin.succ Fin.succ
  rw [residual_anchor basis bit T S z, submatrix_factors T U V c hfac S] at hsub
  rw [hfull] at hsub
  omega


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
  rintro ⟨k, s, g, hs, hodd, hlarge, basis, bit, hbit, T, hT, hcover⟩
  exact PEqualNP.Outside.L_meta_26032_aux.impossible k s g hodd hlarge basis bit hbit T hT hcover
