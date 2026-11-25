import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace PEqualNP.Outside.L_meta_4970

namespace H4OrBlock

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma expand_bound {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (A : Finset ℕ) (good : ℕ → Prop)
    (split : ∀ w, good w → 1 < (S w).card → w ∈ A ∧
      ∃ a b, a < w ∧ b < w ∧ good a ∧ good b ∧ S w = S a ∪ S b)
    (k : ℕ) (W : Finset ℕ)
    (hw : ∀ w ∈ W, good w ∧ (1 < (S w).card → w < k)) :
    (W.biUnion S).card ≤ W.card + (A.filter (· < k)).card := by
  induction k generalizing W with
  | zero =>
    have hsum : (∑ w ∈ W, (S w).card) ≤ ∑ _w ∈ W, 1 := by
      apply Finset.sum_le_sum
      intro w h
      by_contra! hbig
      exact (Nat.not_lt_zero w) ((hw w h).2 hbig)
    simpa using le_trans Finset.card_biUnion_le hsum
  | succ k ih =>
    by_cases hk : k ∈ W ∧ 1 < (S k).card
    · obtain ⟨hkA, a, b, ha, hb, hga, hgb, hab⟩ :=
        split k (hw k hk.1).1 hk.2
      let W' := insert a (insert b (W.erase k))
      have hW' : ∀ w ∈ W', good w ∧ (1 < (S w).card → w < k) := by
        intro w hm
        simp only [W', Finset.mem_insert, Finset.mem_erase] at hm
        rcases hm with rfl | rfl | ⟨hne, hm⟩
        · exact ⟨hga, fun _ => ha⟩
        · exact ⟨hgb, fun _ => hb⟩
        · exact ⟨(hw w hm).1, fun h => by have := (hw w hm).2 h; omega⟩
      have hsub : W.biUnion S ⊆ W'.biUnion S := by
        intro z hz
        obtain ⟨w, hm, hz⟩ := Finset.mem_biUnion.mp hz
        apply Finset.mem_biUnion.mpr
        by_cases he : w = k
        · subst w
          rw [hab, Finset.mem_union] at hz
          exact hz.elim (fun h => ⟨a, by simp [W'], h⟩) (fun h => ⟨b, by simp [W'], h⟩)
        · exact ⟨w, by simp [W', he, hm], hz⟩
      have hcard : W'.card ≤ W.card + 1 := by
        have h₁ := Finset.card_insert_le a (insert b (W.erase k))
        have h₂ := Finset.card_insert_le b (W.erase k)
        have h₃ := Finset.card_erase_add_one hk.1
        change W'.card ≤ _ at h₁
        omega
      have hfilter : A.filter (· < k + 1) = insert k (A.filter (· < k)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hm, hl⟩
          by_cases he : w = k
          · exact Or.inl he
          · exact Or.inr ⟨hm, by omega⟩
        · rintro (rfl | ⟨hm, hl⟩)
          · exact ⟨hkA, by omega⟩
          · exact ⟨hm, by omega⟩
      have hrec := ih W' hW'
      have hle := Finset.card_le_card hsub
      rw [hfilter, Finset.card_insert_of_notMem (by simp)]
      omega
    · have hrec := ih W (fun w hm => ⟨(hw w hm).1, fun h => by
        have hlt := (hw w hm).2 h
        have hne : w ≠ k := fun he => hk (he ▸ ⟨hm, h⟩)
        omega⟩)
      have hs : A.filter (· < k) ⊆ A.filter (· < k + 1) := by
        intro w hw
        obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨hm, by omega⟩
      exact hrec.trans (Nat.add_le_add_left (Finset.card_le_card hs) _)

private lemma fold_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma fold_prefix {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private def stage {α : Type*} (op : α → α → α) (bad : α)
    (seed : List α) (gs : List (ℕ × ℕ)) : List α :=
  gs.foldl (fun w p => w ++ [op (w.getD p.1 bad) (w.getD p.2 bad)]) seed

private lemma stage_length {α : Type*} (op : α → α → α) (bad : α)
    (seed : List α) (gs : List (ℕ × ℕ)) :
    (stage op bad seed gs).length = seed.length + gs.length :=
  fold_length _ _ _

private lemma stage_prefix {α : Type*} (op : α → α → α) (bad : α)
    (seed : List α) (gs : List (ℕ × ℕ)) {w : ℕ} (hw : w < seed.length) :
    (stage op bad seed gs).getD w bad = seed.getD w bad :=
  fold_prefix _ _ _ _ _ hw

private lemma missing {α : Type*} (s : List α) (d : α) {w : ℕ} (hw : s.length ≤ w) :
    s.getD w d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw]
  rfl

private lemma stage_gate {α : Type*} (op : α → α → α) (bad : α)
    (seed : List α) (gs : List (ℕ × ℕ)) {j : ℕ} (hj : j < gs.length) :
    let w := seed.length + j
    let g := gs[j]
    let read := fun i => if i < w then (stage op bad seed gs).getD i bad else bad
    (stage op bad seed gs).getD w bad = op (read g.1) (read g.2) := by
  dsimp only
  let pre := stage op bad seed (gs.take j)
  let g := gs[j]
  have hlen : pre.length = seed.length + j := by
    rw [stage_length, List.length_take, Nat.min_eq_left hj.le]
  have hgs : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  let v := op (pre.getD g.1 bad) (pre.getD g.2 bad)
  have hsplit : stage op bad seed gs = stage op bad (pre ++ [v]) (gs.drop (j + 1)) := by
    conv_lhs => rw [hgs]
    simp only [stage, List.foldl_append, List.foldl_cons, pre, v]
  have hplen : (pre ++ [v]).length = seed.length + j + 1 := by
    rw [List.length_append, List.length_singleton, hlen]
  have hgate : (stage op bad seed gs).getD (seed.length + j) bad = v := by
    rw [hsplit, stage_prefix op bad (pre ++ [v]) _ (by omega), ← hlen,
      List.getD_eq_getElem?_getD]
    simp
  have hr (i : ℕ) : pre.getD i bad =
      if i < seed.length + j then (stage op bad seed gs).getD i bad else bad := by
    split
    · rename_i hi
      rw [hsplit, stage_prefix op bad (pre ++ [v]) _ (by omega)]
      symm
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rfl
    · rename_i hi
      exact missing _ _ (by omega)
  rw [hgate]
  exact congrArg₂ op (hr g.1) (hr g.2)

private lemma map_getD {α β : Type*} (f : α → β) (s : List α) (bad : α) (w : ℕ) :
    (s.map f).getD w (f bad) = f (s.getD w bad) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases s[w]? <;> rfl

private lemma stage_map {α β : Type*} (f : α → β) (op : α → α → α) (op' : β → β → β)
    (hf : ∀ a b, f (op a b) = op' (f a) (f b))
    (bad : α) (seed : List α) (gs : List (ℕ × ℕ)) :
    (stage op bad seed gs).map f = stage op' (f bad) (seed.map f) gs := by
  induction gs generalizing seed with
  | nil => rfl
  | cons p gs ih =>
    simp only [stage, List.foldl_cons] at ih ⊢
    rw [ih, List.map_append, List.map_singleton, hf, map_getD, map_getD]

private def gateList (op : GateOp) (gs : List (ℕ × ℕ)) : List Gate :=
  gs.map fun p => ⟨op, [p.1, p.2]⟩

private lemma stage_eval (op : GateOp) (f : Bool → Bool → Bool)
    (hf : ∀ a b, op.eval [a, b] = f a b) (seed : List Bool) (gs : List (ℕ × ℕ)) :
    (gateList op gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      seed = stage f false seed gs := by
  induction gs generalizing seed with
  | nil => rfl
  | cons p gs ih =>
    simp only [gateList, List.map_cons, List.foldl_cons, List.map_nil, stage, hf] at ih ⊢
    exact ih _

private def gateWires (n : ℕ) (gs : List (ℕ × ℕ)) : Finset ℕ :=
  (Finset.range gs.length).image (n + ·)

private lemma gateWires_card (n : ℕ) (gs : List (ℕ × ℕ)) :
    (gateWires n gs).card = gs.length := by
  unfold gateWires
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h), Finset.card_range]

private def support {n : ℕ} (os : List (ℕ × ℕ)) (w : ℕ) : Finset (Fin n) :=
  (stage (· ∪ ·) ∅ (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) os).getD w ∅

private def hit {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) : Bool :=
  decide (∃ i ∈ s, x i = true)

private lemma or_eval {n : ℕ} (os : List (ℕ × ℕ)) (x : Fin n → Bool) (w : ℕ) :
    (stage (· || ·) false (List.ofFn x) os).getD w false = hit x (support os w) := by
  have hmap := stage_map (hit x) (· ∪ ·) (· || ·) (fun a b => by
    simp [hit, Finset.mem_union, or_and_right, exists_or]) ∅
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) os
  have hseed : (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))).map (hit x) = List.ofFn x := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp [hit]
  rw [hseed, show hit x ∅ = false by simp [hit]] at hmap
  rw [← hmap]
  simpa only [support, show hit x ∅ = false by simp [hit]] using
    map_getD (hit x) (stage (· ∪ ·) ∅
      (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) os) ∅ w

private def leaves (n : ℕ) (gs : List (ℕ × ℕ)) (w : ℕ) : Finset (Option ℕ) :=
  (stage (· ∪ ·) {none} (List.ofFn fun i : Fin n => ({some i.val} : Finset (Option ℕ))) gs).getD
    w {none}

private def allHit (f : ℕ → Bool) (s : Finset (Option ℕ)) : Bool :=
  decide (∀ i ∈ s, i.elim false f = true)

private lemma and_eval (seed : List Bool) (gs : List (ℕ × ℕ)) (w : ℕ) :
    (stage (· && ·) false seed gs).getD w false =
      allHit (fun i => seed.getD i false) (leaves seed.length gs w) := by
  let f := allHit (fun i => seed.getD i false)
  have hmap := stage_map f (· ∪ ·) (· && ·) (fun a b => by
    simp [f, allHit, Finset.mem_union, or_imp, forall_and]) {none}
    (List.ofFn fun i : Fin seed.length => ({some i.val} : Finset (Option ℕ))) gs
  have hseed : (List.ofFn fun i : Fin seed.length => ({some i.val} : Finset (Option ℕ))).map f =
      seed := by
    rw [List.map_ofFn]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [f, allHit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hseed, show f {none} = false by simp [f, allHit]] at hmap
  rw [← hmap]
  simpa only [leaves, show f {none} = false by simp [f, allHit]] using
    map_getD f (stage (· ∪ ·) {none}
      (List.ofFn fun i : Fin seed.length => ({some i.val} : Finset (Option ℕ))) gs) {none} w

private lemma circuit_clauses {n : ℕ} {C : Circuit} {os as : List (ℕ × ℕ)}
    (hg : C.gates = gateList .or os ++ gateList .and as) (x : Fin n → Bool) :
    circuitFun n C x = true ↔
      ∀ i ∈ leaves (n + os.length) as C.output,
        i.elim false (fun w => hit x (support os w)) = true := by
  let seed := stage (· || ·) false (List.ofFn x) os
  have hlen : seed.length = n + os.length := by rw [stage_length, List.length_ofFn]
  change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
  unfold Circuit.wires
  rw [hg, List.foldl_append,
    stage_eval .or (· || ·) (fun a b => by simp [GateOp.eval]),
    stage_eval .and (· && ·) (fun a b => by simp [GateOp.eval])]
  change (stage (· && ·) false seed as).getD C.output false = true ↔ _
  rw [and_eval, hlen]
  simp only [allHit, decide_eq_true_eq, seed, or_eval]

private lemma bound_one {α : Type*} [DecidableEq α]
    (S : ℕ → Finset α) (A : Finset ℕ) (good : ℕ → Prop)
    (split : ∀ w, good w → 1 < (S w).card → w ∈ A ∧
      ∃ a b, a < w ∧ b < w ∧ good a ∧ good b ∧ S w = S a ∪ S b)
    (w : ℕ) (hw : good w) : (S w).card ≤ A.card + 1 := by
  have h := expand_bound S A good split (w + 1) {w} (by simpa using hw)
  have hl := Finset.card_filter_le A (· < w + 1)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at h
  omega

private lemma or_split {n : ℕ} {α : Type*} [DecidableEq α]
    (os : List (ℕ × ℕ)) (proj : Finset (Fin n) → Finset α)
    (he : proj ∅ = ∅) (hs : ∀ i, (proj {i}).card ≤ 1) (w : ℕ)
    (hw : 1 < (proj (support os w)).card) :
    w ∈ gateWires n os ∧
      ∃ a b, a < w ∧ b < w ∧ support (n := n) os w = support os a ∪ support os b := by
  let seed := List.ofFn fun i : Fin n => ({i} : Finset (Fin n))
  have hlen : seed.length = n := List.length_ofFn
  by_cases hpre : w < n
  · have hh : support (n := n) os w = {⟨w, hpre⟩} := by
      unfold support
      rw [stage_prefix _ _ _ _ (by simpa only [List.length_ofFn] using hpre)]
      simp [List.getD_eq_getElem?_getD, hpre]
    rw [hh] at hw
    exact False.elim (Nat.not_lt_of_ge (hs _) hw)
  by_cases hg : w < n + os.length
  · let j := w - n
    have hj : j < os.length := by omega
    have hwj : w = n + j := by omega
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, hwj.symm⟩, ?_⟩
    have hgate := stage_gate (· ∪ ·) ∅ seed os hj
    dsimp only at hgate
    rw [hlen, ← hwj] at hgate
    change support os w =
      (if os[j].1 < w then support os os[j].1 else ∅) ∪
      (if os[j].2 < w then support os os[j].2 else ∅) at hgate
    by_cases ha : os[j].1 < w <;> by_cases hb : os[j].2 < w
    · exact ⟨_, _, ha, hb, by simpa [ha, hb] using hgate⟩
    · exact ⟨_, _, ha, ha, by simpa [ha, hb] using hgate⟩
    · exact ⟨_, _, hb, hb, by simpa [ha, hb] using hgate⟩
    · rw [show support os w = ∅ by simpa [ha, hb] using hgate, he] at hw
      simp at hw
  · have hh : support (n := n) os w = ∅ := by
      unfold support
      apply missing
      rw [stage_length, List.length_ofFn]
      omega
    rw [hh, he] at hw
    simp at hw

private lemma or_count {n : ℕ} {α : Type*} [DecidableEq α]
    (os : List (ℕ × ℕ)) (proj : Finset (Fin n) → Finset α)
    (he : proj ∅ = ∅) (hs : ∀ i, (proj {i}).card ≤ 1)
    (hu : ∀ s t, proj (s ∪ t) = proj s ∪ proj t)
    (P : Finset (Fin n) → Prop) [DecidablePred P]
    (down : ∀ {s t}, s ⊆ t → P t → P s)
    (w : ℕ) (hw : P (support os w)) :
    (proj (support os w)).card ≤
      ((gateWires n os).filter fun i => 1 < (proj (support os i)).card ∧
        P (support os i)).card + 1 := by
  apply bound_one _ _ (fun i => P (support os i)) _ w hw
  intro v hv hb
  obtain ⟨hm, a, b, ha, hb', heq⟩ := or_split os proj he hs v hb
  refine ⟨Finset.mem_filter.mpr ⟨hm, hb, hv⟩, a, b, ha, hb', ?_, ?_, ?_⟩
  · exact down (heq.symm ▸ Finset.subset_union_left) hv
  · exact down (heq.symm ▸ Finset.subset_union_right) hv
  · rw [heq, hu]

private def project {n m : ℕ} (emb : Fin m → Fin n) (s : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => emb i ∈ s

private lemma mem_project {n m : ℕ} {emb : Fin m → Fin n} {s : Finset (Fin n)} {i : Fin m} :
    i ∈ project emb s ↔ emb i ∈ s := by simp [project]

private lemma project_mono {n m : ℕ} (emb : Fin m → Fin n) {s t : Finset (Fin n)}
    (h : s ⊆ t) : project emb s ⊆ project emb t :=
  fun _ hi => mem_project.mpr (h (mem_project.mp hi))

private lemma project_empty {n m : ℕ} (emb : Fin m → Fin n) : project emb ∅ = ∅ := by
  ext i
  simp [mem_project]

private lemma project_singleton {n m : ℕ} {emb : Fin m → Fin n} (he : Function.Injective emb)
    (i : Fin n) : (project emb {i}).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply he
  exact (Finset.mem_singleton.mp (mem_project.mp ha)).trans
    (Finset.mem_singleton.mp (mem_project.mp hb)).symm

private lemma project_union {n m : ℕ} (emb : Fin m → Fin n) (s t : Finset (Fin n)) :
    project emb (s ∪ t) = project emb s ∪ project emb t := by
  ext i
  simp only [Finset.mem_union, mem_project]

private def bits {l r : ℕ} (L : Finset (Fin l)) (R : Finset (Fin r)) :
    Fin (l + r) → Bool :=
  Fin.addCases (fun i => decide (i ∈ L)) (fun i => decide (i ∈ R))

private lemma bits_left {l r : ℕ} (L : Finset (Fin l)) (R : Finset (Fin r)) (i : Fin l) :
    bits L R (Fin.castAdd r i) = true ↔ i ∈ L := by simp [bits]

private lemma bits_right {l r : ℕ} (L : Finset (Fin l)) (R : Finset (Fin r)) (i : Fin r) :
    bits L R (Fin.natAdd l i) = true ↔ i ∈ R := by simp [bits]

private lemma hit_bits {l r : ℕ} (L : Finset (Fin l)) (R : Finset (Fin r))
    (s : Finset (Fin (l + r))) :
    hit (bits L R) s = true ↔
      (∃ i ∈ project (Fin.castAdd r) s, i ∈ L) ∨
      (∃ j ∈ project (Fin.natAdd l) s, j ∈ R) := by
  simp only [hit, decide_eq_true_eq, mem_project]
  constructor
  · rintro ⟨i, hi, hx⟩
    induction i using Fin.addCases with
    | left a => exact Or.inl ⟨a, hi, (bits_left L R a).mp hx⟩
    | right b => exact Or.inr ⟨b, hi, (bits_right L R b).mp hx⟩
  · rintro (⟨i, hi, hx⟩ | ⟨j, hj, hx⟩)
    · exact ⟨_, hi, (bits_left L R i).mpr hx⟩
    · exact ⟨_, hj, (bits_right L R j).mpr hx⟩

private lemma rejected_clause {l r : ℕ} {C : Circuit} {os as : List (ℕ × ℕ)}
    (hg : C.gates = gateList .or os ++ gateList .and as)
    (hnone : none ∉ leaves (l + r + os.length) as C.output)
    (L : Finset (Fin l)) (R : Finset (Fin r))
    (hr : ¬ circuitFun (l + r) C (bits L R) = true) :
    ∃ w, some w ∈ leaves (l + r + os.length) as C.output ∧
      ¬ hit (bits L R) (support os w) = true := by
  by_contra! h
  apply hr
  apply (circuit_clauses hg _).mpr
  intro z hz
  cases z with
  | none => exact (hnone hz).elim
  | some w => exact h w hz

private lemma or_block_count {l r : ℕ} {C : Circuit} {os as : List (ℕ × ℕ)}
    (hg : C.gates = gateList .or os ++ gateList .and as)
    (G E : Finset (Fin l × Fin r))
    (hc4 : ∀ a b : Fin l, ∀ i j : Fin r, a ≠ b → i ≠ j →
      ¬ ((a, i) ∈ G ∧ (a, j) ∈ G ∧ (b, i) ∈ G ∧ (b, j) ∈ G))
    (hsound : ∀ x : Fin (l + r) → Bool, circuitFun (l + r) C x = true →
      ∃ p ∈ G, x (Fin.castAdd r p.1) = true ∧ x (Fin.natAdd l p.2) = true)
    (hacc : ∀ p ∈ E, circuitFun (l + r) C (bits {p.1} {p.2}) = true) :
    E.card ≤ os.length + 1 := by
  classical
  by_cases hE : E.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hE
    simp [he]
  let F := leaves (l + r + os.length) as C.output
  let Ls : Finset (Fin (l + r)) → Finset (Fin l) := project (Fin.castAdd r)
  let Rs : Finset (Fin (l + r)) → Finset (Fin r) := project (Fin.natAdd l)
  let left (w : ℕ) := Ls (support os w)
  let right (w : ℕ) := Rs (support os w)
  have hnone : none ∉ F := by
    obtain ⟨p, hp⟩ := hE
    intro hn
    have hf := (circuit_clauses hg _).mp (hacc p hp) none hn
    simp at hf
  have cover : ∀ w, some w ∈ F → ∀ p ∈ E, p.1 ∈ left w ∨ p.2 ∈ right w := by
    intro w hw p hp
    have ht : hit (bits {p.1} {p.2}) (support os w) = true :=
      (circuit_clauses hg _).mp (hacc p hp) (some w) hw
    obtain (⟨i, hi, he⟩ | ⟨j, hj, he⟩) := (hit_bits _ _ _).mp ht
    · exact Or.inl (Finset.mem_singleton.mp he ▸ hi)
    · exact Or.inr (Finset.mem_singleton.mp he ▸ hj)
  have reject (L : Finset (Fin l)) (R : Finset (Fin r))
      (h : ∀ p ∈ G, p.1 ∈ L → p.2 ∉ R) :
      ¬ circuitFun (l + r) C (bits L R) = true := by
    intro ht
    obtain ⟨p, hp, hL, hR⟩ := hsound _ ht
    exact h p hp ((bits_left L R p.1).mp hL) ((bits_right L R p.2).mp hR)
  obtain ⟨w₀, hw₀, hmiss₀⟩ := rejected_clause hg hnone ∅ Finset.univ
    (reject ∅ Finset.univ (by simp))
  have hpure : right w₀ = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact hmiss₀ ((hit_bits _ _ _).mpr (Or.inr ⟨j, hj, Finset.mem_univ j⟩))
  let U := E.image Prod.fst
  have hU : U ⊆ left w₀ := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    exact (cover w₀ hw₀ p hp).resolve_right (by simp [hpure])
  let N := fun u : Fin l => Finset.univ.filter fun j : Fin r => (u, j) ∈ E
  have hN (u : Fin l) : ∃ w, some w ∈ F ∧ N u ⊆ right w ∧
      ∀ j ∈ right w, (u, j) ∈ G := by
    let R := Finset.univ.filter fun j : Fin r => (u, j) ∉ G
    have hr := reject {u} R (by
      intro p hp hpu
      have he := Finset.mem_singleton.mp hpu
      have hh : (p.1, p.2) ∈ G := hp
      simpa [R, ← he] using hh)
    obtain ⟨w, hw, hmiss⟩ := rejected_clause hg hnone {u} R hr
    have hnot : u ∉ left w := fun hu =>
      hmiss ((hit_bits _ _ _).mpr (Or.inl ⟨u, hu, Finset.mem_singleton_self u⟩))
    refine ⟨w, hw, ?_, ?_⟩
    · intro j hj
      exact (cover w hw (u, j) ((Finset.mem_filter.mp hj).2)).resolve_left hnot
    · intro j hj
      by_contra hn
      exact hmiss ((hit_bits _ _ _).mpr (Or.inr ⟨j, hj, by simp [R, hn]⟩))
  choose w hwF hwN hwG using hN
  let O := gateWires (l + r) os
  let A₀ := O.filter fun i => 1 < (left i).card ∧ right i = ∅
  let A := fun u : Fin l => O.filter fun i =>
    1 < (right i).card ∧ ∀ j ∈ right i, (u, j) ∈ G
  have h₀ : U.card ≤ A₀.card + 1 := by
    apply (Finset.card_le_card hU).trans
    exact or_count os Ls (project_empty _) (project_singleton (Fin.castAdd_injective _ _))
      (project_union _) (fun s => Rs s = ∅)
      (fun h ht => Finset.subset_empty.mp (ht ▸ project_mono _ h)) w₀ hpure
  have hA (u : Fin l) : (N u).card ≤ (A u).card + 1 := by
    apply (Finset.card_le_card (hwN u)).trans
    exact or_count os Rs (project_empty _) (project_singleton (Fin.natAdd_injective _ _))
      (project_union _) (fun s => ∀ j ∈ Rs s, (u, j) ∈ G)
      (fun h ht j hj => ht j (project_mono _ h hj)) (w u) (hwG u)
  have pairwise : (↑U : Set (Fin l)).PairwiseDisjoint A := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro v ha hb
    obtain ⟨_, hv, hga⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, _, hgb⟩ := Finset.mem_filter.mp hb
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hv
    exact hc4 a b i j hab hij ⟨hga i hi, hga j hj, hgb i hi, hgb j hj⟩
  have disj : Disjoint A₀ (U.biUnion A) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨_, _, hempty⟩ := Finset.mem_filter.mp hv
    obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hv'
    have hbig := (Finset.mem_filter.mp hu).2.1
    simp [hempty] at hbig
  have hbudget : A₀.card + ∑ u ∈ U, (A u).card ≤ os.length := by
    rw [← Finset.card_biUnion pairwise, ← Finset.card_union_of_disjoint disj,
      ← gateWires_card (l + r) os]
    apply Finset.card_le_card
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (Finset.mem_filter.mp hi).1
    · obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hi
      exact (Finset.mem_filter.mp hu).1
  have hEcard : E.card = ∑ u ∈ U, (N u).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (fun p hp => Finset.mem_image_of_mem Prod.fst hp : ∀ p ∈ E, p.1 ∈ U)]
    apply Finset.sum_congr rfl
    intro u _
    apply le_antisymm
    · refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
      · intro p hp
        obtain ⟨hm, he⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [← he] using hm⟩
      · intro p hp q hq he
        exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
    · refine Finset.card_le_card_of_injOn (fun j => (u, j)) ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩
      · intro _ _ _ _ h
        exact congrArg Prod.snd h
  have hsum : E.card ≤ (∑ u ∈ U, (A u).card) + U.card := by
    have hconst : (∑ _u ∈ U, (1 : ℕ)) = U.card := by simp
    rw [hEcard, ← hconst, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun u _ => hA u)
  omega

private lemma edge_bits {l r : ℕ} (p : Fin l × Fin r) :
    (fun i : Fin (l + r) => decide (i = Fin.castAdd r p.1 ∨ i = Fin.natAdd l p.2)) =
      bits {p.1} {p.2} := by
  funext i
  have disj (a : Fin l) (b : Fin r) : Fin.castAdd r a ≠ Fin.natAdd l b := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have ha := a.isLt
    omega
  induction i using Fin.addCases with
  | left a =>
    simp [bits, disj, (Fin.castAdd_injective l r).eq_iff]
  | right b =>
    simp [bits, (disj _ b).symm, (Fin.natAdd_injective _ _).eq_iff]


lemma or_then_and_edge_count {l r : ℕ} (G E : Finset (Fin l × Fin r))
    (C : Circuit) (os as : List (ℕ × ℕ))
    (hc4 : ∀ a b : Fin l, ∀ i j : Fin r, a ≠ b → i ≠ j →
      ¬ ((a, i) ∈ G ∧ (a, j) ∈ G ∧ (b, i) ∈ G ∧ (b, j) ∈ G))
    (hg : C.gates =
      os.map (fun p => { op := GateOp.or, inputs := [p.1, p.2] }) ++
      as.map (fun p => { op := GateOp.and, inputs := [p.1, p.2] }))
    (hsound : ∀ x : Fin (l + r) → Bool, circuitFun (l + r) C x = true →
      ∃ p ∈ G, x (Fin.castAdd r p.1) = true ∧ x (Fin.natAdd l p.2) = true)
    (hacc : ∀ p ∈ E, circuitFun (l + r) C
      (fun i => decide (i = Fin.castAdd r p.1 ∨ i = Fin.natAdd l p.2)) = true) :
    E.card ≤ os.length + 1 := by
  apply or_block_count hg G E hc4 hsound
  intro p hp
  simpa only [edge_bits] using hacc p hp

lemma or_then_and_or_count {l r : ℕ} (G E : Finset (Fin l × Fin r))
    (C : Circuit) (os as : List (ℕ × ℕ))
    (hc4 : ∀ a b : Fin l, ∀ i j : Fin r, a ≠ b → i ≠ j →
      ¬ ((a, i) ∈ G ∧ (a, j) ∈ G ∧ (b, i) ∈ G ∧ (b, j) ∈ G))
    (hg : C.gates =
      os.map (fun p => { op := GateOp.or, inputs := [p.1, p.2] }) ++
      as.map (fun p => { op := GateOp.and, inputs := [p.1, p.2] }))
    (hsound : ∀ x : Fin (l + r) → Bool, circuitFun (l + r) C x = true →
      ∃ p ∈ G, x (Fin.castAdd r p.1) = true ∧ x (Fin.natAdd l p.2) = true)
    (hacc : ∀ p ∈ E, circuitFun (l + r) C
      (fun i => decide (i = Fin.castAdd r p.1 ∨ i = Fin.natAdd l p.2)) = true) :
    E.card ≤ (C.gates.filter fun g => match g.op with
      | .or => true
      | _ => false).length + 1 := by
  have h := or_then_and_edge_count G E C os as hc4 hg hsound hacc
  simpa [hg, List.filter_map, Function.comp_def] using h

end H4OrBlock

namespace SafeBirth

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def single (v : α ⊕ β) : α ⊕ β → Bool := fun w => decide (w = v)

def pair (u v : α ⊕ β) : α ⊕ β → Bool := fun w => decide (w = u ∨ w = v)

def adjacent (E : α → β → Prop) : α ⊕ β → α ⊕ β → Prop
  | .inl a, .inr b => E a b
  | .inr b, .inl a => E a b
  | _, _ => False

lemma single_le_pair_left (u v : α ⊕ β) : single u ≤ pair u v := by
  intro w
  by_cases h : w = u <;> simp [single, pair, h]

lemma single_le_pair_right (u v : α ⊕ β) : single v ≤ pair u v := by
  intro w
  by_cases h : w = v <;> simp [single, pair, h]

lemma safe_singletons_adjacent (E : α → β → Prop)
    (f g : (α ⊕ β → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (hsafe : ∀ x, f x = true → g x = true →
      ∃ a b, E a b ∧ x (.inl a) = true ∧ x (.inr b) = true)
    (u v : α ⊕ β) (hu : f (single u) = true) (hv : g (single v) = true) :
    adjacent E u v := by
  have hfu := hf (single_le_pair_left u v)
  have hgv := hg (single_le_pair_right u v)
  rw [hu] at hfu
  rw [hv] at hgv
  have hfu' : f (pair u v) = true :=
    le_antisymm (by cases f (pair u v) <;> decide) hfu
  have hgv' : g (pair u v) = true :=
    le_antisymm (by cases g (pair u v) <;> decide) hgv
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe (pair u v) hfu' hgv'
  cases u with
  | inl u =>
    cases v with
    | inl v => simp [pair] at hb
    | inr v =>
      have hau : a = u := by simpa [pair] using ha
      have hbv : b = v := by simpa [pair] using hb
      simpa [adjacent, hau, hbv] using hab
  | inr u =>
    cases v with
    | inl v =>
      have hav : a = v := by simpa [pair] using ha
      have hbu : b = u := by simpa [pair] using hb
      simpa [adjacent, hav, hbu] using hab
    | inr v => simp [pair] at ha

def fresh (f g : (α ⊕ β → Bool) → Bool) (a : α) (b : β) : Prop :=
  (f (single (.inl a)) = true ∧ g (single (.inr b)) = true) ∨
    (g (single (.inl a)) = true ∧ f (single (.inr b)) = true)

lemma safe_fresh_edges_share_endpoint (E : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (E a b ∧ E a b' ∧ E a' b ∧ E a' b'))
    (f g : (α ⊕ β → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (hsafe : ∀ x, f x = true → g x = true →
      ∃ a b, E a b ∧ x (.inl a) = true ∧ x (.inr b) = true)
    {a a' : α} {b b' : β} (hfirst : fresh f g a b)
    (hsecond : fresh f g a' b') : a = a' ∨ b = b' := by
  by_contra hne
  have haa : a ≠ a' := fun h => hne (Or.inl h)
  have hbb : b ≠ b' := fun h => hne (Or.inr h)
  rcases hfirst with ⟨hfa, hgb⟩ | ⟨hga, hfb⟩
  · rcases hsecond with ⟨hfa', hgb'⟩ | ⟨hga', hfb'⟩
    · apply hfour a a' b b' haa hbb
      exact ⟨safe_singletons_adjacent E f g hf hg hsafe _ _ hfa hgb,
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfa hgb',
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfa' hgb,
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfa' hgb'⟩
    · exact safe_singletons_adjacent E f g hf hg hsafe _ _ hfa hga'
  · rcases hsecond with ⟨hfa', hgb'⟩ | ⟨hga', hfb'⟩
    · exact safe_singletons_adjacent E f g hf hg hsafe _ _ hfa' hga
    · apply hfour a a' b b' haa hbb
      exact ⟨safe_singletons_adjacent E f g hf hg hsafe _ _ hfb hga,
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfb' hga,
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfb hga',
        safe_singletons_adjacent E f g hf hg hsafe _ _ hfb' hga'⟩

end SafeBirth

namespace BirthObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 2 × Fin 2) := {(0, 0), (0, 1), (1, 1)}

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.and, [0, 0]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [6, 8]⟩], 9⟩

def value (j : ℕ) (x : Fin 4 → Bool) : Bool :=
  (circuit.wires (List.ofFn x)).getD (4 + j) false

def singleton (i : Fin 4) : Fin 4 → Bool := fun k => decide (k = i)

def pair (a b : Fin 2) : Fin 4 → Bool :=
  fun k => decide (k = Fin.castAdd 2 a ∨ k = Fin.natAdd 2 b)

def born (a b : Fin 2) (j : ℕ) : Prop :=
  value j (pair a b) = true ∧
    value j (singleton (Fin.castAdd 2 a)) = false ∧
    value j (singleton (Fin.natAdd 2 b)) = false

lemma no_four_cycle :
    ∀ a a' b b' : Fin 2, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧
        (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma is_ao2 : PEqualNP.TopForm.IsAO2 4 circuit := by
  decide +kernel

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = decide (∃ a b : Fin 2,
      (a, b) ∈ edges ∧ x (Fin.castAdd 2 a) = true ∧
        x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma no_mixed_or :
    PEqualNP.TwoColour.tCount 4 circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

lemma right_star : ∀ x : Fin 4 → Bool,
    value 1 x = decide (∃ b ∈ (Finset.univ : Finset (Fin 2)),
      x (Fin.natAdd 2 b) = true) := by
  decide +kernel

lemma left_star : ∀ x : Fin 4 → Bool,
    value 0 x = decide (∃ a ∈ (Finset.univ : Finset (Fin 2)),
      x (Fin.castAdd 2 a) = true) := by
  decide +kernel

lemma stars_serve_all_edges : ∀ a b : Fin 2, (a, b) ∈ edges →
    (∃ j : ℕ, ∃ Q : Finset (Fin 2),
      j < circuit.gates.length ∧ (NestedCover.gateAt circuit j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ edges) ∧
      ∀ x : Fin 4 → Bool, value j x = decide (∃ b' ∈ Q,
        x (Fin.natAdd 2 b') = true)) ∨
    (∃ j : ℕ, ∃ P : Finset (Fin 2),
      j < circuit.gates.length ∧ (NestedCover.gateAt circuit j).op = GateOp.or ∧
      2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ edges) ∧
      ∀ x : Fin 4 → Bool, value j x = decide (∃ a' ∈ P,
        x (Fin.castAdd 2 a') = true)) := by
  have hcover : ∀ a b : Fin 2, (a, b) ∈ edges → a = 0 ∨ b = 1 := by
    decide +kernel
  intro a b hab
  rcases hcover a b hab with rfl | rfl
  · exact Or.inl ⟨1, Finset.univ, by decide, rfl, by decide,
      Finset.mem_univ b, by decide +kernel, right_star⟩
  · exact Or.inr ⟨0, Finset.univ, by decide, rfl, by decide,
      Finset.mem_univ a, by decide +kernel, left_star⟩

lemma first_birth_collision :
    (0, 0) ∈ edges ∧ (1, 1) ∈ edges ∧
    born 0 0 2 ∧ born 1 1 2 ∧
    (∀ j : Fin 2, ¬ born 0 0 j) ∧
    (∀ j : Fin 2, ¬ born 1 1 j) := by
  unfold born
  decide +kernel

lemma birth_gate_accepts_nonedge :
    value 2 (pair 1 0) = true ∧ circuitFun 4 circuit (pair 1 0) = false := by
  decide +kernel

lemma size_six : circuit.size = 6 := by
  rfl

end BirthObstruction

namespace FamilySafety

variable {α β ι : Type*} [Fintype ι]

lemma whole_factor_of_choice_hitting (E : α → β → Prop)
    (A : ι → Finset α) (b : β)
    (hhit : ∀ f : ι → α, (∀ i, f i ∈ A i) → ∃ i, E (f i) b) :
    ∃ i, ∀ a ∈ A i, E a b := by
  classical
  by_contra h
  push Not at h
  choose f hf hbad using h
  obtain ⟨i, hi⟩ := hhit f hf
  exact hbad i hi

lemma choice_hitting_bound (E : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (E a b ∧ E a b' ∧ E a' b ∧ E a' b'))
    (A : ι → Finset α) (hlarge : ∀ i, 2 ≤ (A i).card)
    (B : Finset β)
    (hhit : ∀ b ∈ B, ∀ f : ι → α,
      (∀ i, f i ∈ A i) → ∃ i, E (f i) b) :
    B.card ≤ Fintype.card ι := by
  classical
  have hfull (b : {b // b ∈ B}) : ∃ i, ∀ a ∈ A i, E a b :=
    whole_factor_of_choice_hitting E A b (hhit b b.property)
  choose factor hfactor using hfull
  have hinj : Function.Injective factor := by
    intro b b' heq
    apply Subtype.ext
    by_contra hne
    obtain ⟨a, ha, a', ha', haa⟩ :=
      Finset.one_lt_card.mp (show 1 < (A (factor b)).card by
        have := hlarge (factor b)
        omega)
    apply hfour a a' b b' haa hne
    have ha2 : a ∈ A (factor b') := heq ▸ ha
    have ha2' : a' ∈ A (factor b') := heq ▸ ha'
    exact ⟨hfactor b a ha, hfactor b' a ha2,
      hfactor b a' ha', hfactor b' a' ha2'⟩
  simpa using Fintype.card_le_of_injective factor hinj

lemma safe_left_factors_right_bound (E : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (E a b ∧ E a b' ∧ E a' b ∧ E a' b'))
    (A : ι → Finset α) (hlarge : ∀ i, 2 ≤ (A i).card)
    (B : Finset β)
    (hsafe : ∀ x : α ⊕ β → Bool,
      (∀ i, ∃ a ∈ A i, x (.inl a) = true) →
      (∃ b ∈ B, x (.inr b) = true) →
      ∃ a b, E a b ∧ x (.inl a) = true ∧ x (.inr b) = true) :
    B.card ≤ Fintype.card ι := by
  classical
  apply choice_hitting_bound E hfour A hlarge B
  intro b hb f hf
  let x : α ⊕ β → Bool
    | .inl a => decide (∃ i, f i = a)
    | .inr b' => decide (b' = b)
  have hleft : ∀ i, ∃ a ∈ A i, x (.inl a) = true := by
    intro i
    exact ⟨f i, hf i, by simp [x]⟩
  have hright : ∃ b ∈ B, x (.inr b) = true := ⟨b, hb, by simp [x]⟩
  obtain ⟨a, b', hab, ha, hb'⟩ := hsafe x hleft hright
  have hbb : b' = b := by simpa [x] using hb'
  have hfa : ∃ i, f i = a := by simpa [x] using ha
  obtain ⟨i, rfl⟩ := hfa
  exact ⟨i, hbb ▸ hab⟩

lemma triple_hitting_bound (E : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (E a b ∧ E a b' ∧ E a' b ∧ E a' b'))
    (A Q : Finset α) (hA : 2 ≤ A.card) (hQ : 2 ≤ Q.card)
    (B : Finset β)
    (hhit : ∀ a ∈ A, ∀ q ∈ Q, ∀ b ∈ B, E a b ∨ E q b) :
    B.card ≤ 2 := by
  let family : Bool → Finset α := fun i => if i then Q else A
  have hlarge : ∀ i, 2 ≤ (family i).card := by
    intro i
    cases i <;> simp [family, hA, hQ]
  have h := choice_hitting_bound E hfour family hlarge B
    (fun b hb f hf => by
      have ha : f false ∈ A := by simpa [family] using hf false
      have hq : f true ∈ Q := by simpa [family] using hf true
      rcases hhit (f false) ha (f true) hq b hb with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩)
  simpa using h

end FamilySafety

namespace H4OrErase

def conjunction {α : Type*} [DecidableEq α] (M : Finset α) (x : α → Bool) : Bool :=
  decide (∀ i ∈ M, x i = true)

def singleton {α : Type*} [DecidableEq α] (i : α) : α → Bool :=
  fun j => decide (j = i)

def star {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

def before {α : Type*} [DecidableEq α] (F : (α → Bool) → Bool → Bool)
    (A : (α → Bool) → Bool) (M : Finset α) (x : α → Bool) : Bool :=
  F x (A x || conjunction M x)

def after {α : Type*} (F : (α → Bool) → Bool → Bool)
    (A : (α → Bool) → Bool) (x : α → Bool) : Bool := F x (A x)

lemma conjunction_singleton_false {α : Type*} [DecidableEq α]
    (M : Finset α) (hM : 2 ≤ M.card) (i : α) :
    conjunction M (singleton i) = false := by
  apply decide_eq_false
  intro h
  have hs : M ⊆ {i} := by
    intro j hj
    have hj' := h j hj
    simpa [singleton] using hj'
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega

lemma before_eq_after_singleton {α : Type*} [DecidableEq α]
    (F : (α → Bool) → Bool → Bool) (A : (α → Bool) → Bool)
    (M : Finset α) (hM : 2 ≤ M.card) (i : α) :
    before F A M (singleton i) = after F A (singleton i) := by
  simp [before, after, conjunction_singleton_false M hM]

lemma after_le_before {α : Type*} [DecidableEq α]
    (F : (α → Bool) → Bool → Bool) (A : (α → Bool) → Bool)
    (M : Finset α) (hF : ∀ x, Monotone (F x)) (x : α → Bool) :
    after F A x ≤ before F A M x := by
  apply hF x
  cases A x <;> cases conjunction M x <;> decide

lemma after_monotone {α : Type*}
    (F : (α → Bool) → Bool → Bool) (A : (α → Bool) → Bool)
    (hF : Monotone (fun z : (α → Bool) × Bool => F z.1 z.2))
    (hA : Monotone A) : Monotone (after F A) := by
  intro x y hxy
  change F x (A x) ≤ F y (A y)
  exact hF (a := (x, A x)) (b := (y, A y)) ⟨hxy, hA hxy⟩

lemma pure_star_preserved {α : Type*} [DecidableEq α]
    (F : (α → Bool) → Bool → Bool) (A : (α → Bool) → Bool)
    (M Q : Finset α) (hM : 2 ≤ M.card)
    (hF : Monotone (fun z : (α → Bool) × Bool => F z.1 z.2))
    (hA : Monotone A) (hstar : ∀ x, before F A M x = star Q x) :
    ∀ x, after F A x = star Q x := by
  intro x
  apply le_antisymm
  · rw [← hstar x]
    apply after_le_before F A M _ x
    intro y b c hbc
    exact hF (a := (y, b)) (b := (y, c)) ⟨le_refl y, hbc⟩
  · cases hx : star Q x with
    | false => exact Bool.false_le _
    | true =>
        have hex : ∃ i ∈ Q, x i = true := of_decide_eq_true hx
        obtain ⟨i, hi, hxi⟩ := hex
        have hle : singleton i ≤ x := by
          intro j
          by_cases hji : j = i
          · subst j
            simp [singleton, hxi]
          · simp [singleton, hji]
        have hpos : after F A (singleton i) = true := by
          rw [← before_eq_after_singleton F A M hM i, hstar]
          simp [star, singleton, hi]
        have hh := after_monotone F A hF hA hle
        rw [hpos] at hh
        exact hh

def edgeInput {p l : ℕ} (e : Fin p × Fin l) : Fin (p + l) → Bool :=
  fun i => decide (i = Fin.castAdd l e.1 ∨ i = Fin.natAdd p e.2)

lemma opposite_ne {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  have ha := a.isLt
  omega

lemma conjunction_edge_eq {p l : ℕ} (M : Finset (Fin (p + l)))
    (hM : 2 ≤ M.card) (e : Fin p × Fin l)
    (he : conjunction M (edgeInput e) = true) :
    M = {Fin.castAdd l e.1, Fin.natAdd p e.2} := by
  have hs : M ⊆ {Fin.castAdd l e.1, Fin.natAdd p e.2} := by
    intro i hi
    have hforall : ∀ j ∈ M, edgeInput e j = true := by
      simpa only [conjunction, decide_eq_true_eq] using he
    have hx : edgeInput e i = true := hforall i hi
    simpa [edgeInput] using hx
  apply Finset.eq_of_subset_of_card_le hs
  simpa [opposite_ne] using hM

lemma conjunction_edge_unique {p l : ℕ} (M : Finset (Fin (p + l)))
    (hM : 2 ≤ M.card) (e f : Fin p × Fin l)
    (he : conjunction M (edgeInput e) = true)
    (hf : conjunction M (edgeInput f) = true) : e = f := by
  have hp := (conjunction_edge_eq M hM e he).symm.trans (conjunction_edge_eq M hM f hf)
  have hl : Fin.castAdd l e.1 ∈ ({Fin.castAdd l f.1, Fin.natAdd p f.2} :
      Finset (Fin (p + l))) := by
    rw [← hp]
    simp
  have hr : Fin.natAdd p e.2 ∈ ({Fin.castAdd l f.1, Fin.natAdd p f.2} :
      Finset (Fin (p + l))) := by
    rw [← hp]
    simp
  have ha : e.1 = f.1 := by
    have hh : Fin.castAdd l e.1 = Fin.castAdd l f.1 ∨
        Fin.castAdd l e.1 = Fin.natAdd p f.2 := by simpa using hl
    exact Fin.castAdd_injective _ _ (hh.resolve_right (opposite_ne _ _))
  have hb : e.2 = f.2 := by
    have hh : Fin.natAdd p e.2 = Fin.castAdd l f.1 ∨
        Fin.natAdd p e.2 = Fin.natAdd p f.2 := by simpa using hr
    exact Fin.natAdd_injective _ _ (hh.resolve_left (opposite_ne _ _).symm)
  exact Prod.ext ha hb

lemma lost_edges_card_le_one {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool)
    (A : (Fin (p + l) → Bool) → Bool)
    (M : Finset (Fin (p + l))) (hM : 2 ≤ M.card)
    (E : Finset (Fin p × Fin l)) :
    (E.filter fun e => before F A M (edgeInput e) = true ∧
      after F A (edgeInput e) = false).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  have monomial_true (e : Fin p × Fin l)
      (h : before F A M (edgeInput e) = true ∧ after F A (edgeInput e) = false) :
      conjunction M (edgeInput e) = true := by
    cases hm : conjunction M (edgeInput e) with
    | false =>
        have hh : before F A M (edgeInput e) = after F A (edgeInput e) := by
          simp [before, after, hm]
        rw [hh, h.2] at h
        simp at h
    | true => rfl
  exact conjunction_edge_unique M hM e f
    (monomial_true e (Finset.mem_filter.mp he).2)
    (monomial_true f (Finset.mem_filter.mp hf).2)

lemma accepted_edge_budget {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool)
    (A : (Fin (p + l) → Bool) → Bool)
    (M : Finset (Fin (p + l))) (hM : 2 ≤ M.card)
    (E : Finset (Fin p × Fin l))
    (hE : ∀ e ∈ E, before F A M (edgeInput e) = true) :
    E.card ≤ (E.filter fun e => after F A (edgeInput e) = true).card + 1 := by
  let good := E.filter fun e => after F A (edgeInput e) = true
  let bad := E.filter fun e => before F A M (edgeInput e) = true ∧
    after F A (edgeInput e) = false
  have hb : bad.card ≤ 1 := lost_edges_card_le_one F A M hM E
  have hdisj : Disjoint good bad := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have ht := (Finset.mem_filter.mp he).2
    have hz := (Finset.mem_filter.mp hf).2.2
    exact Bool.noConfusion (ht.symm.trans hz)
  have heq : E = good ∪ bad := by
    ext e
    constructor
    · intro he
      cases hv : after F A (edgeInput e) with
      | false => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hE e he, hv⟩)
      | true => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hv⟩)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · exact (Finset.mem_filter.mp he).1
      · exact (Finset.mem_filter.mp he).1
  have hc : E.card = good.card + bad.card := by rw [heq, Finset.card_union_of_disjoint hdisj]
  change E.card ≤ good.card + 1
  omega

end H4OrErase

namespace H4SingletonMerge

def singleton {α : Type*} [DecidableEq α] (i : α) : α → Bool :=
  fun j => decide (j = i)

def edgeInput {p l : ℕ} (e : Fin p × Fin l) : Fin (p + l) → Bool :=
  fun i => decide (i = Fin.castAdd l e.1 ∨ i = Fin.natAdd p e.2)

def mergeBefore {p l : ℕ} (F : (Fin (p + l) → Bool) → Bool → Bool)
    (u v : Fin p) (x : Fin (p + l) → Bool) : Bool :=
  F x (x (Fin.castAdd l u) || x (Fin.castAdd l v))

def mergeAfter {p l : ℕ} (F : (Fin (p + l) → Bool) → Bool → Bool)
    (u : Fin p) (x : Fin (p + l) → Bool) : Bool := F x (x (Fin.castAdd l u))

lemma opposite_ne {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  have ha := a.isLt
  omega

lemma edge_left {p l : ℕ} (e : Fin p × Fin l) (a : Fin p) :
    edgeInput e (Fin.castAdd l a) = decide (a = e.1) := by
  simp [edgeInput, opposite_ne, (Fin.castAdd_injective p l).eq_iff]

lemma singleton_right_le_edge {p l : ℕ} (a : Fin p) (b : Fin l) :
    singleton (Fin.natAdd p b) ≤ edgeInput (a, b) := by
  intro i
  by_cases hi : i = Fin.natAdd p b
  · subst i
    simp [singleton, edgeInput]
  · simp [singleton, hi]

private lemma true_of_le {b : Bool} (h : true ≤ b) : b = true := by
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) h)
  | true => rfl

lemma lost_edge_left_eq {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p)
    (e : Fin p × Fin l)
    (hbefore : mergeBefore F u v (edgeInput e) = true)
    (hafter : mergeAfter F u (edgeInput e) = false) : e.1 = v := by
  by_cases hv : v = e.1
  · exact hv.symm
  · have hxv : edgeInput e (Fin.castAdd l v) = false := by simp [edge_left, hv]
    have heq : mergeBefore F u v (edgeInput e) = mergeAfter F u (edgeInput e) := by
      simp [mergeBefore, mergeAfter, hxv]
    rw [heq, hafter] at hbefore
    contradiction

lemma context_singleton_common_neighbor {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p)
    (G : Finset (Fin p × Fin l))
    (hF : Monotone (fun x => F x true))
    (hsound : ∀ e : Fin p × Fin l, mergeBefore F u v (edgeInput e) = true → e ∈ G)
    (b : Fin l) (hb : F (singleton (Fin.natAdd p b)) true = true) :
    (u, b) ∈ G ∧ (v, b) ∈ G := by
  have ht (a : Fin p) : F (edgeInput (a, b)) true = true := by
    have hh := hF (singleton_right_le_edge a b)
    dsimp only at hh
    rw [hb] at hh
    exact true_of_le hh
  constructor
  · apply hsound (u, b)
    simpa [mergeBefore, edge_left] using ht u
  · apply hsound (v, b)
    simpa [mergeBefore, edge_left] using ht v

lemma linear_lost_edges_card_le_one {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p) (huv : u ≠ v)
    (G E : Finset (Fin p × Fin l))
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ G ∧ (a, b') ∈ G ∧ (a', b) ∈ G ∧ (a', b') ∈ G))
    (hF : Monotone (fun x => F x true))
    (hsound : ∀ e : Fin p × Fin l, mergeBefore F u v (edgeInput e) = true → e ∈ G) :
    (E.filter fun e => mergeBefore F u v (edgeInput e) = true ∧
      mergeAfter F u (edgeInput e) = false ∧
      F (singleton (Fin.natAdd p e.2)) true = true).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨_, heb, hea, hec⟩ := Finset.mem_filter.mp he
  obtain ⟨_, hfb, hfa, hfc⟩ := Finset.mem_filter.mp hf
  have hev := lost_edge_left_eq F u v e heb hea
  have hfv := lost_edge_left_eq F u v f hfb hfa
  have heN := context_singleton_common_neighbor F u v G hF hsound e.2 hec
  have hfN := context_singleton_common_neighbor F u v G hF hsound f.2 hfc
  have hright : e.2 = f.2 := by
    by_contra hne
    exact hc4 u v e.2 f.2 huv hne ⟨heN.1, hfN.1, heN.2, hfN.2⟩
  exact Prod.ext (hev.trans hfv.symm) hright

lemma lost_edge_pair_context {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p)
    (e : Fin p × Fin l)
    (hsingle : ∀ i : Fin (p + l), mergeBefore F u v (singleton i) = false)
    (hbefore : mergeBefore F u v (edgeInput e) = true)
    (hafter : mergeAfter F u (edgeInput e) = false)
    (hcontext : F (singleton (Fin.natAdd p e.2)) true = false) :
    F (edgeInput e) true = true ∧
      F (singleton (Fin.castAdd l e.1)) true = false ∧
      F (singleton (Fin.natAdd p e.2)) true = false := by
  have hev := lost_edge_left_eq F u v e hbefore hafter
  have hxv : edgeInput e (Fin.castAdd l v) = true := by simp [edge_left, hev]
  refine ⟨?_, ?_, hcontext⟩
  · simpa [mergeBefore, hxv] using hbefore
  · rw [hev]
    simpa [mergeBefore, singleton] using hsingle (Fin.castAdd l v)

end H4SingletonMerge

namespace H4ContextBound

def mergeBefore {p l : ℕ} (F : (Fin (p + l) → Bool) → Bool → Bool)
    (u v : Fin p) (x : Fin (p + l) → Bool) : Bool :=
  F x (x (Fin.castAdd l u) || x (Fin.castAdd l v))

def addPoint {p l : ℕ} (u : Fin p) (x : Fin (p + l) → Bool) : Fin (p + l) → Bool :=
  fun i => x i || decide (i = Fin.castAdd l u)

lemma opposite_ne {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  have ha := a.isLt
  omega

lemma addPoint_le {p l : ℕ} (u : Fin p) (x : Fin (p + l) → Bool) :
    x ≤ addPoint u x := by
  intro i
  change x i ≤ x i ⊔ decide (i = Fin.castAdd l u)
  exact le_sup_left

lemma addPoint_self {p l : ℕ} (u : Fin p) (x : Fin (p + l) → Bool) :
    addPoint u x (Fin.castAdd l u) = true := by simp [addPoint]

lemma addPoint_right {p l : ℕ} (u : Fin p) (x : Fin (p + l) → Bool) (b : Fin l) :
    addPoint u x (Fin.natAdd p b) = x (Fin.natAdd p b) := by
  simp [addPoint, (opposite_ne u b).symm]

lemma addPoint_left {p l : ℕ} (u : Fin p) (x : Fin (p + l) → Bool) (a : Fin p) :
    addPoint u x (Fin.castAdd l a) = (x (Fin.castAdd l a) || decide (a = u)) := by
  simp [addPoint, (Fin.castAdd_injective p l).eq_iff]

private lemma true_of_le {b : Bool} (h : true ≤ b) : b = true := by
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) h)
  | true => rfl

lemma independent_context_neighbors {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p)
    (G : Finset (Fin p × Fin l))
    (hF : Monotone (fun x => F x true))
    (hsound : ∀ x : Fin (p + l) → Bool, mergeBefore F u v x = true →
      ∃ a b, (a, b) ∈ G ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)
    (x : Fin (p + l) → Bool) (hx : F x true = true)
    (hind : ¬ ∃ a b, (a, b) ∈ G ∧ x (Fin.castAdd l a) = true ∧
      x (Fin.natAdd p b) = true) :
    (∃ b, (u, b) ∈ G ∧ x (Fin.natAdd p b) = true) ∧
      (∃ b, (v, b) ∈ G ∧ x (Fin.natAdd p b) = true) := by
  have ht (w : Fin p) : F (addPoint w x) true = true := by
    have hh := hF (addPoint_le w x)
    dsimp only at hh
    rw [hx] at hh
    exact true_of_le hh
  have hu : mergeBefore F u v (addPoint u x) = true := by
    simpa [mergeBefore, addPoint_self] using ht u
  have hv : mergeBefore F u v (addPoint v x) = true := by
    simpa [mergeBefore, addPoint_self] using ht v
  have extract (w : Fin p)
      (hw : ∃ a b, (a, b) ∈ G ∧ addPoint w x (Fin.castAdd l a) = true ∧
        addPoint w x (Fin.natAdd p b) = true) :
      ∃ b, (w, b) ∈ G ∧ x (Fin.natAdd p b) = true := by
    obtain ⟨a, b, hab, ha, hb⟩ := hw
    rw [addPoint_right] at hb
    by_cases haw : a = w
    · subst a
      exact ⟨b, hab, hb⟩
    · have hax : x (Fin.castAdd l a) = true := by
        simpa [addPoint_left, haw] using ha
      exact False.elim (hind ⟨a, b, hab, hax, hb⟩)
  exact ⟨extract u (hsound _ hu), extract v (hsound _ hv)⟩

lemma context_upper_bound {p l : ℕ}
    (F : (Fin (p + l) → Bool) → Bool → Bool) (u v : Fin p)
    (G : Finset (Fin p × Fin l))
    (hF : Monotone (fun x => F x true))
    (hsound : ∀ x : Fin (p + l) → Bool, mergeBefore F u v x = true →
      ∃ a b, (a, b) ∈ G ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)
    (x : Fin (p + l) → Bool) (hx : F x true = true) :
    (∃ a b, (a, b) ∈ G ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) ∨
      ((∃ b, (u, b) ∈ G ∧ x (Fin.natAdd p b) = true) ∧
        (∃ b, (v, b) ∈ G ∧ x (Fin.natAdd p b) = true)) := by
  by_cases h : ∃ a b, (a, b) ∈ G ∧ x (Fin.castAdd l a) = true ∧
    x (Fin.natAdd p b) = true
  · exact Or.inl h
  · exact Or.inr (independent_context_neighbors F u v G hF hsound x hx h)

end H4ContextBound

namespace Orientation

lemma distinct_representatives_of_two
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (t : α → Finset β) (hlarge : ∀ a, 2 ≤ (t a).card)
    (hdegree : ∀ b, (Finset.univ.filter fun a => b ∈ t a).card ≤ 2) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, f a ∈ t a := by
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp
  intro s
  let r : α → β → Prop := fun a b => b ∈ t a
  have hleft : ∀ a ∈ s, 2 ≤ ((s.biUnion t).bipartiteAbove r a).card := by
    intro a ha
    have heq : (s.biUnion t).bipartiteAbove r a = t a := by
      ext b
      simp only [Finset.mem_bipartiteAbove, Finset.mem_biUnion, r]
      constructor
      · exact fun h => h.2
      · exact fun hb => ⟨⟨a, ha, hb⟩, hb⟩
    rw [heq]
    exact hlarge a
  have hright : ∀ b ∈ s.biUnion t, (s.bipartiteBelow r b).card ≤ 2 := by
    intro b _
    apply le_trans (Finset.card_le_card ?_) (hdegree b)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,
      (Finset.mem_filter.mp ha).2⟩
  have hcount := Finset.card_nsmul_le_card_nsmul (R := ℕ) r hleft hright
  simp only [nsmul_eq_mul, Nat.cast_id] at hcount
  omega

lemma surjective_serving_orientation
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (t : α → Finset β) (hlarge : ∀ a, 2 ≤ (t a).card)
    (hdegree : ∀ b, (Finset.univ.filter fun a => b ∈ t a).card ≤ 2)
    (hcover : ∀ b, ∃ a, b ∈ t a) :
    ∃ orient : β → α, Function.Surjective orient ∧ ∀ b, b ∈ t (orient b) := by
  classical
  obtain ⟨f, hf, hft⟩ := distinct_representatives_of_two t hlarge hdegree
  let orient : β → α := fun b =>
    if h : ∃ a, f a = b then Classical.choose h else Classical.choose (hcover b)
  have hleft : ∀ a, orient (f a) = a := by
    intro a
    have he : ∃ a', f a' = f a := ⟨a, rfl⟩
    dsimp only [orient]
    rw [dite_eq_left he]
    exact hf (Classical.choose_spec he)
  refine ⟨orient, fun a => ⟨f a, hleft a⟩, ?_⟩
  intro b
  dsimp only [orient]
  split_ifs with h
  · have heq := Classical.choose_spec h
    simpa only [heq] using hft (Classical.choose h)
  · exact Classical.choose_spec (hcover b)

lemma serving_orientation_of_endpoints
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (A : Finset V) (serves : V → B → Prop) [DecidableRel serves]
    (ends : B → Finset V) (hends : ∀ b, (ends b).card ≤ 2)
    (hinc : ∀ a b, serves a b → a ∈ ends b)
    (hlarge : ∀ a ∈ A, 2 ≤ (Finset.univ.filter fun b => serves a b).card)
    (hcover : ∀ b, ∃ a ∈ A, serves a b) :
    ∃ orient : B → A, Function.Surjective orient ∧ ∀ b, serves (orient b) b := by
  classical
  let t : A → Finset B := fun a => Finset.univ.filter fun b => serves a b
  have ht : ∀ a, 2 ≤ (t a).card := fun a => hlarge a a.property
  have hd : ∀ b, (Finset.univ.filter fun a : A => b ∈ t a).card ≤ 2 := by
    intro b
    have hi : (Finset.univ.filter fun a : A => b ∈ t a).card ≤ (ends b).card := by
      apply Finset.card_le_card_of_injOn (fun a : A => (a : V))
      · intro a ha
        exact hinc a b (Finset.mem_filter.mp (Finset.mem_filter.mp ha).2).2
      · intro a _ a' _ h
        exact Subtype.ext h
    exact hi.trans (hends b)
  have hc : ∀ b, ∃ a, b ∈ t a := by
    intro b
    obtain ⟨a, ha, hab⟩ := hcover b
    exact ⟨⟨a, ha⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hab⟩⟩
  obtain ⟨orient, ho, ht⟩ := surjective_serving_orientation t ht hd hc
  exact ⟨orient, ho, fun b => (Finset.mem_filter.mp (ht b)).2⟩

end Orientation

namespace H4PostfilterObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : Finset (Fin 2 × Fin 4) := {(0, 0), (0, 1), (1, 2), (1, 3)}

def circuit : Circuit :=
  { gates := [
      ⟨.or, [0, 1]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [0, 0]⟩,
      ⟨.and, [1, 1]⟩,
      ⟨.or, [9, 8]⟩,
      ⟨.or, [7, 10]⟩,
      ⟨.or, [7, 8]⟩,
      ⟨.and, [6, 11]⟩,
      ⟨.and, [14, 12]⟩,
      ⟨.and, [15, 13]⟩],
    output := 16 }

def graphValue (x : Fin 6 → Bool) : Bool :=
  decide (∃ (a : Fin 2) (b : Fin 4), (a, b) ∈ edges ∧
    x (Fin.castAdd 4 a) = true ∧ x (Fin.natAdd 2 b) = true)

lemma edges_no_four : ∀ (a a' : Fin 2) (b b' : Fin 4), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide +kernel

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma circuit_computes : ∀ x : Fin 6 → Bool, circuitFun 6 circuit x = graphValue x := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma circuit_t_zero : PEqualNP.TwoColour.tCount 6 circuit (fun i => decide (2 ≤ i)) = 0 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma served_left : ∀ (a : Fin 2) (b : Fin 4), (a, b) ∈ edges →
    ∃ (j : ℕ) (Q : Finset (Fin 4)), j < circuit.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt circuit j).op = GateOp.or ∧
      2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ edges) ∧
      ∀ x : Fin 6 → Bool,
        (circuit.wires (List.ofFn x)).getD (6 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 2 b') = true) := by
  intro a b hab
  fin_cases a
  · refine ⟨1, {0, 1}, by decide, by rfl, by decide, ?_, by decide, by decide +kernel⟩
    fin_cases b <;> simp [edges] at hab ⊢
  · refine ⟨2, {2, 3}, by decide, by rfl, by decide, ?_, by decide, by decide +kernel⟩
    fin_cases b <;> simp [edges] at hab ⊢

lemma circuit_size : circuit.size = 11 := rfl

lemma edges_card : edges.card = 4 := by decide

def counterfactual : Circuit :=
  { gates := ⟨.and, []⟩ :: circuit.gates.tail, output := 16 }

def allLeaves : Fin 6 → Bool := fun i => decide (2 ≤ i.val)

def edgeInput (e : Fin 2 × Fin 4) : Fin 6 → Bool :=
  fun i => decide (i = Fin.castAdd 4 e.1 ∨ i = Fin.natAdd 2 e.2)

def wireValue (w : Fin 17) (x : Fin 6 → Bool) : Bool :=
  (counterfactual.wires (List.ofFn x)).getD w.val false

noncomputable def wireConjunction (S : Finset (Fin 17)) (x : Fin 6 → Bool) : Bool :=
  S.toList.all (fun w => wireValue w x)

lemma wireConjunction_spec (S : Finset (Fin 17)) (x : Fin 6 → Bool) :
    wireConjunction S x = true ↔ ∀ w ∈ S, wireValue w x = true := by
  simp only [wireConjunction, List.all_eq_true, Finset.mem_toList]

noncomputable def postfilter (S : Finset (Fin 17)) (x : Fin 6 → Bool) : Bool :=
  circuitFun 6 counterfactual x && wireConjunction S x

lemma allLeaves_independent : graphValue allLeaves = false := by decide +kernel

lemma counterfactual_allLeaves : circuitFun 6 counterfactual allLeaves = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma false_wires_at_allLeaves : ∀ w : Fin 17, wireValue w allLeaves = false ↔
    w = 0 ∨ w = 1 ∨ w = 9 ∨ w = 10 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma false_wire_rejects_star : ∀ w : Fin 17, wireValue w allLeaves = false →
    (∀ b : Fin 4, wireValue w (edgeInput (0, b)) = false) ∨
      (∀ b : Fin 4, wireValue w (edgeInput (1, b)) = false) := by
  decide +kernel

lemma bool_false_of_not_true (b : Bool) (h : b ≠ true) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

lemma postfilter_false_of_wire_false (S : Finset (Fin 17)) (w : Fin 17) (hw : w ∈ S)
    (x : Fin 6 → Bool) (hx : wireValue w x = false) : postfilter S x = false := by
  have hc : wireConjunction S x = false := by
    apply bool_false_of_not_true
    intro hh
    have ht := (wireConjunction_spec S x).mp hh w hw
    exact (by decide : false ≠ true) (hx.symm.trans ht)
  simp [postfilter, hc]

lemma not_all_true_has_false {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → Bool) (h : ¬ ∀ w ∈ S, f w = true) :
    ∃ w ∈ S, f w = false := by
  push Not at h
  obtain ⟨w, hw, hf⟩ := h
  refine ⟨w, hw, ?_⟩
  cases hx : f w with
  | false => rfl
  | true => exact False.elim (hf hx)

lemma rejecting_postfilter_has_false_wire (S : Finset (Fin 17))
    (h : postfilter S allLeaves = false) :
    ∃ w ∈ S, wireValue w allLeaves = false := by
  have hc : wireConjunction S allLeaves = false := by
    simpa only [postfilter, counterfactual_allLeaves, Bool.true_and] using h
  have hn : ¬ ∀ w ∈ S, wireValue w allLeaves = true := by
    intro hall
    exact (by decide : false ≠ true)
      (hc.symm.trans ((wireConjunction_spec S allLeaves).mpr hall))
  exact not_all_true_has_false S (fun w => wireValue w allLeaves) hn

lemma rejecting_postfilter_rejects_star (S : Finset (Fin 17))
    (h : postfilter S allLeaves = false) :
    (∀ b : Fin 4, postfilter S (edgeInput (0, b)) = false) ∨
      (∀ b : Fin 4, postfilter S (edgeInput (1, b)) = false) := by
  obtain ⟨w, hw, hfalse⟩ := rejecting_postfilter_has_false_wire S h
  rcases false_wire_rejects_star w hfalse with hzero | hone
  · exact Or.inl (fun b => postfilter_false_of_wire_false S w hw _ (hzero b))
  · exact Or.inr (fun b => postfilter_false_of_wire_false S w hw _ (hone b))

lemma accepted_card_le_two_of_reject_star (P : (Fin 2 × Fin 4) → Bool)
    (h : (∀ b : Fin 4, P (0, b) = false) ∨ (∀ b : Fin 4, P (1, b) = false)) :
    (edges.filter fun e => P e = true).card ≤ 2 := by
  rcases h with hzero | hone
  · have hs : edges.filter (fun e => P e = true) ⊆ edges.filter (fun e => e.1 = 1) := by
      intro e he
      obtain ⟨hem, hp⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨hem, ?_⟩
      obtain ⟨a, b⟩ := e
      fin_cases a
      · change P (0, b) = true at hp
        rw [hzero b] at hp
        contradiction
      · rfl
    exact (Finset.card_le_card hs).trans (by decide)
  · have hs : edges.filter (fun e => P e = true) ⊆ edges.filter (fun e => e.1 = 0) := by
      intro e he
      obtain ⟨hem, hp⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨hem, ?_⟩
      obtain ⟨a, b⟩ := e
      fin_cases a
      · rfl
      · change P (1, b) = true at hp
        rw [hone b] at hp
        contradiction
    exact (Finset.card_le_card hs).trans (by decide)

lemma rejecting_postfilter_edge_budget (S : Finset (Fin 17))
    (h : postfilter S allLeaves = false) :
    (edges.filter fun e => postfilter S (edgeInput e) = true).card ≤ 2 :=
  accepted_card_le_two_of_reject_star (fun e => postfilter S (edgeInput e))
    (rejecting_postfilter_rejects_star S h)

lemma sound_postfilter_edge_budget (S : Finset (Fin 17))
    (hsound : ∀ x : Fin 6 → Bool, postfilter S x = true → graphValue x = true) :
    (edges.filter fun e => postfilter S (edgeInput e) = true).card ≤ 2 := by
  have hreject : postfilter S allLeaves = false :=
    bool_false_of_not_true _ (fun hx =>
      (by decide : false ≠ true) (allLeaves_independent.symm.trans (hsound allLeaves hx)))
  exact rejecting_postfilter_edge_budget S hreject

lemma sound_postfilter_cannot_lose_at_most_one (S : Finset (Fin 17))
    (hsound : ∀ x : Fin 6 → Bool, postfilter S x = true → graphValue x = true) :
    ¬ edges.card ≤ (edges.filter fun e => postfilter S (edgeInput e) = true).card + 1 := by
  have hb := sound_postfilter_edge_budget S hsound
  rw [edges_card]
  omega

end H4PostfilterObstruction



namespace H4SlotCount

lemma two_colour_slot_bound {p l : ℕ} {σ : Type*} [Fintype σ]
    (E M : Finset (Fin p × Fin l))
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (P : σ → Finset (Fin p)) (Q : σ → Finset (Fin l))
    (hmono : ∀ s, P s = ∅ ∨ Q s = ∅)
    (pointSlot lineSlot : {e // e ∈ M} → σ)
    (hpoint : ∀ e, e.val.1 ∈ P (pointSlot e) ∧
      ∀ a ∈ P (pointSlot e), (a, e.val.2) ∈ E)
    (hline : ∀ e, e.val.2 ∈ Q (lineSlot e) ∧
      ∀ b ∈ Q (lineSlot e), (e.val.1, b) ∈ E) :
    2 * M.card ≤ Fintype.card σ := by
  classical
  have hp_inj : Function.Injective pointSlot := by
    intro e f hslot
    apply Subtype.ext
    by_contra hne
    have ha : e.val.1 ≠ f.val.1 := fun h =>
      hne (hleft e.val e.property f.val f.property h)
    have hb : e.val.2 ≠ f.val.2 := fun h =>
      hne (hright e.val e.property f.val f.property h)
    have he := hpoint e
    have hf := hpoint f
    have hea : e.val.1 ∈ P (pointSlot f) := hslot ▸ he.1
    have hfa : f.val.1 ∈ P (pointSlot e) := hslot.symm ▸ hf.1
    exact hc4 e.val.1 f.val.1 e.val.2 f.val.2 ha hb
      ⟨he.2 _ he.1, hf.2 _ hea, he.2 _ hfa, hf.2 _ hf.1⟩
  have hl_inj : Function.Injective lineSlot := by
    intro e f hslot
    apply Subtype.ext
    by_contra hne
    have ha : e.val.1 ≠ f.val.1 := fun h =>
      hne (hleft e.val e.property f.val f.property h)
    have hb : e.val.2 ≠ f.val.2 := fun h =>
      hne (hright e.val e.property f.val f.property h)
    have he := hline e
    have hf := hline f
    have heb : e.val.2 ∈ Q (lineSlot f) := hslot ▸ he.1
    have hfb : f.val.2 ∈ Q (lineSlot e) := hslot.symm ▸ hf.1
    exact hc4 e.val.1 f.val.1 e.val.2 f.val.2 ha hb
      ⟨he.2 _ he.1, he.2 _ hfb, hf.2 _ heb, hf.2 _ hf.1⟩
  have hdisj : ∀ e f, pointSlot e ≠ lineSlot f := by
    intro e f hslot
    have hp := (hpoint e).1
    have hq : f.val.2 ∈ Q (pointSlot e) := hslot.symm ▸ (hline f).1
    rcases hmono (pointSlot e) with h | h
    · rw [h] at hp
      simp at hp
    · rw [h] at hq
      simp at hq
  let embed : ({e // e ∈ M} ⊕ {e // e ∈ M}) → σ := Sum.elim pointSlot lineSlot
  have hinj : Function.Injective embed := by
    intro x y hxy
    cases x with
    | inl e =>
        cases y with
        | inl f => exact congrArg Sum.inl (hp_inj hxy)
        | inr f => exact False.elim (hdisj e f hxy)
    | inr e =>
        cases y with
        | inl f => exact False.elim (hdisj f e hxy.symm)
        | inr f => exact congrArg Sum.inr (hl_inj hxy)
  have hcard := Fintype.card_le_of_injective embed hinj
  simpa only [Fintype.card_sum, Fintype.card_coe, two_mul] using hcard

lemma and_gate_matching_bound {p l : ℕ} {κ : Type*} [Fintype κ]
    (E M : Finset (Fin p × Fin l))
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (P : (κ × Fin 2) → Finset (Fin p)) (Q : (κ × Fin 2) → Finset (Fin l))
    (hmono : ∀ s, P s = ∅ ∨ Q s = ∅)
    (hpoint : ∀ e ∈ M, ∃ s, e.1 ∈ P s ∧ ∀ a ∈ P s, (a, e.2) ∈ E)
    (hline : ∀ e ∈ M, ∃ s, e.2 ∈ Q s ∧ ∀ b ∈ Q s, (e.1, b) ∈ E) :
    M.card ≤ Fintype.card κ := by
  classical
  let pointSlot : {e // e ∈ M} → κ × Fin 2 :=
    fun e => Classical.choose (hpoint e.val e.property)
  let lineSlot : {e // e ∈ M} → κ × Fin 2 :=
    fun e => Classical.choose (hline e.val e.property)
  have hp : ∀ e, e.val.1 ∈ P (pointSlot e) ∧
      ∀ a ∈ P (pointSlot e), (a, e.val.2) ∈ E := by
    intro e
    exact Classical.choose_spec (hpoint e.val e.property)
  have hl : ∀ e, e.val.2 ∈ Q (lineSlot e) ∧
      ∀ b ∈ Q (lineSlot e), (e.val.1, b) ∈ E := by
    intro e
    exact Classical.choose_spec (hline e.val e.property)
  have hh := two_colour_slot_bound E M hleft hright hc4 P Q hmono pointSlot lineSlot hp hl
  simp only [Fintype.card_prod, Fintype.card_fin] at hh
  omega

end H4SlotCount

namespace SeparatingTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Test (n : ℕ) := (Fin n → Bool) → Prop

def binary (b : Bool) (u v : ℕ) : Gate :=
  ⟨if b then .and else .or, [u, v]⟩

def combine {n} (b : Bool) (p q : Test n) : Test n :=
  fun x => if b then p x ∧ q x else p x ∨ q x

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (n : ℕ) (gs : List Gate) (i : ℕ) : Test n :=
  fun x => ((gs.foldl step (List.ofFn x)).getD i false) = true

lemma length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, step]; omega

lemma old_wire {n gs i} (hi : i < n + gs.length) (g : Gate) :
    W n (gs ++ [g]) i = W n gs i := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  simp [W, List.foldl_append, step, List.getD, List.getElem?_append_left (hl ▸ hi : i < (gs.foldl step (List.ofFn x)).length)]

lemma new_wire (n) (gs : List Gate) (b u v) :
    W n (gs ++ [binary b u v]) (n + gs.length) =
      combine b (W n gs u) (W n gs v) := by
  funext x
  have hl := length_fold gs (List.ofFn x)
  simp only [List.length_ofFn] at hl
  cases b <;> simp [W, List.foldl_append, step, binary, GateOp.eval, combine,
    ← hl, List.getD]

def Layout (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i (hi : i < gs.length), ∃ b u v, gs[i] = binary b u v ∧ u < n+i ∧ v < n+i

lemma layout_of {n} {C : Circuit} (h : IsAO2 n C) : Layout n C.gates := by
  intro i hi
  have hm := List.getElem_mem (l := C.gates) hi
  obtain ⟨u,v, huv⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  have hat : gateAt C i = C.gates[i] := by simp [gateAt, List.getD, hi]
  have hr := h.2.1 i hi
  rw [hat, huv] at hr
  obtain ho | ho := h.1 _ hm
  · exact ⟨true,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩
  · exact ⟨false,u,v, by cases hg : C.gates[i] with | mk o l => simp_all [binary],
      hr u (by simp), hr v (by simp)⟩

lemma old_wire_append {n : ℕ} (gs hs : List Gate) {i : ℕ}
    (hi : i < n + gs.length) : W n (gs ++ hs) i = W n gs i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, old_wire (by simp; omega), ih]

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨j, hj, hr, ho, hi⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma orIn_gate (n : ℕ) (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    orIn n C (n + j) = @ite (Finset (Fin n)) ((gateAt C j).op = .or) (Classical.propDecidable _)
      ((gateAt C j).inputs.toFinset.biUnion (orIn n C)) ∅ := by
  classical
  ext a
  rw [mem_orIn]
  by_cases hop : (gateAt C j).op = .or
  · simp only [hop, ↓reduceIte, Finset.mem_biUnion]
    constructor
    · rintro (he | ⟨k, hk, hr, hok, hai⟩)
      · have := a.isLt
        omega
      · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨_, w, hw, hlt, hrw⟩⟩
        · subst k
          exact ⟨a.val, List.mem_toFinset.mpr hai, orIn_self n C a⟩
        · exact ⟨w, List.mem_toFinset.mpr hw,
            (mem_orIn n C w a).mpr (Or.inr ⟨k, hk, hrw, hok, hai⟩)⟩
    · rintro ⟨w, hw, haw⟩
      have hw' := List.mem_toFinset.mp hw
      exact (mem_orIn n C (n+j) a).mp
        (orIn_up n C j w a hj hop hw' (hC j hj w hw') haw)
  · simp only [hop, ↓reduceIte]
    simp only [Finset.notMem_empty, iff_false]
    rintro (he | ⟨k, hk, hr, hok, hai⟩)
    · have := a.isLt
      omega
    · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨ho, _⟩⟩
      · subst k
        exact hop hok
      · exact hop ho

lemma W_input {n : ℕ} (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    W n gs i x ↔ x i = true := by
  change W n ([] ++ gs) i x ↔ x i = true
  rw [old_wire_append [] gs i.isLt]
  simp [W, List.getD]

lemma W_gate {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ b u v, gateAt C j = binary b u v ∧ u < n + j ∧ v < n + j ∧
      W n C.gates (n+j) = combine b (W n C.gates u) (W n C.gates v) := by
  obtain ⟨b,u,v,hg,hu,hv⟩ := layout_of hC j hj
  refine ⟨b,u,v,by simpa [gateAt,List.getD,hj] using hg,hu,hv,?_⟩
  have hlen : (C.gates.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj.le]
  have hsplit : C.gates = (C.gates.take j ++ [binary b u v]) ++ C.gates.drop (j+1) := by
    rw [← hg, List.append_assoc]
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hroot : W n C.gates (n+j) = W n (C.gates.take j ++ [binary b u v]) (n+j) := by
    conv_lhs => rw [hsplit]
    exact old_wire_append _ _ (by simp [hlen])
  have hchild (w : ℕ) (hw : w < n+j) : W n C.gates w = W n (C.gates.take j) w := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    exact old_wire_append _ _ (by simpa [hlen] using hw)
  have hnew := new_wire n (C.gates.take j) b u v
  rw [hlen] at hnew
  rw [hroot, hnew, ← hchild u hu, ← hchild v hv]

lemma separating_trace {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → W n C.gates w x → ¬ W n C.gates w y →
      ∃ i : Fin n, x i = true ∧ y i = false ∧
        (i ∈ orIn n C w ∨ ∃ j < C.gates.length,
          (gateAt C j).op = .and ∧ ∃ z ∈ (gateAt C j).inputs,
            i ∈ orIn n C z ∧ ¬ W n C.gates z y) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx hy
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      have hix : x i = true := (W_input C.gates i x).mp hx
      have hiy : y i = false := by
        cases h : y i with
        | false => rfl
        | true => exact False.elim (hy ((W_input C.gates i y).mpr h))
      exact ⟨i, hix, hiy, Or.inl (orIn_self n C i)⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
      have choose_child : ∃ z, z ∈ [u,v] ∧ z < n+j ∧
          W n C.gates z x ∧ ¬ W n C.gates z y := by
        rw [heval] at hx hy
        cases b with
        | false =>
          have hxx : W n C.gates u x ∨ W n C.gates v x := by simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∧ ¬ W n C.gates v y := by
            simpa [combine, not_or] using hy
          rcases hxx with h | h
          · exact ⟨u, by simp, hu, h, hyy.1⟩
          · exact ⟨v, by simp, hv, h, hyy.2⟩
        | true =>
          have hxx : W n C.gates u x ∧ W n C.gates v x := by simpa [combine] using hx
          have hyy : ¬ W n C.gates u y ∨ ¬ W n C.gates v y :=
            not_and_or.mp (by simpa [combine] using hy)
          rcases hyy with h | h
          · exact ⟨u, by simp, hu, hxx.1, h⟩
          · exact ⟨v, by simp, hv, hxx.2, h⟩
      obtain ⟨z,hzm,hzlt,hzx,hzy⟩ := choose_child
      obtain ⟨i,hix,hiy,hraw | hslot⟩ := ih z hzlt (hzlt.trans hw) hzx hzy
      · refine ⟨i,hix,hiy,?_⟩
        have hmem : z ∈ (gateAt C j).inputs := by simpa [hgate,binary] using hzm
        cases b with
        | false =>
          exact Or.inl (orIn_up n C j z i hj (by simp [hgate,binary]) hmem hzlt hraw)
        | true =>
          exact Or.inr ⟨j,hj,by simp [hgate,binary],z,hmem,hraw,hzy⟩
      · exact ⟨i,hix,hiy,Or.inr hslot⟩

lemma orIn_semantics {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → ∀ i ∈ orIn n C w,
      x i = true → W n C.gates w x := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw i hi hix
    by_cases hin : w < n
    · rw [orIn_input n C w hin, Finset.mem_singleton] at hi
      subst i
      exact (W_input C.gates ⟨w,hin⟩ x).mpr hix
    · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b,u,v,hgate,hu,hv,heval⟩ := W_gate hC j hj
      have hr := orIn_gate n C hC.2.1 j hj
      rw [hr] at hi
      cases b with
      | true => simp [hgate,binary] at hi
      | false =>
        have hmem : i ∈ orIn n C u ∨ i ∈ orIn n C v := by
          simpa [hgate,binary] using hi
        rw [heval]
        change W n C.gates u x ∨ W n C.gates v x
        exact hmem.elim
          (fun h => Or.inl (ih u hu (hu.trans hw) i h hix))
          (fun h => Or.inr (ih v hv (hv.trans hw) i h hix))

lemma separating_slot {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hx : W n C.gates w x) (hy : ¬ W n C.gates w y)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (hsingle : ¬ W n C.gates w (fun k => decide (k = i))) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ z ∈ (gateAt C j).inputs, i ∈ orIn n C z ∧ ¬ W n C.gates z y := by
  obtain ⟨k,hkx,hky,hraw | hslot⟩ := separating_trace C hC x y w hw hx hy
  · have hki := hunique k hkx hky
    subst k
    exact False.elim (hsingle (orIn_semantics C hC _ w hw i hraw (by simp)))
  · exact hunique k hkx hky ▸ hslot

lemma slot_members_false {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (y : Fin n → Bool) (z : ℕ) (hz : z < n + C.gates.length)
    (hfalse : ¬ W n C.gates z y) : ∀ i ∈ orIn n C z, y i = false := by
  intro i hi
  cases h : y i with
  | false => rfl
  | true => exact False.elim (hfalse (orIn_semantics C hC y z hz i hi h))

lemma orIn_colour_equal {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (colour : ℕ → Bool) (hT : PEqualNP.TwoColour.tCount n C colour = 0)
    (w : ℕ) (hw : w < n + C.gates.length)
    (i k : Fin n) (hi : i ∈ orIn n C w) (hk : k ∈ orIn n C w) :
    colour i = colour k := by
  classical
  by_cases hin : w < n
  · rw [orIn_input n C w hin, Finset.mem_singleton] at hi hk
    rw [hi, hk]
  · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < C.gates.length := by omega
    have hor : (gateAt C j).op = .or := by
      by_contra hop
      rw [orIn_gate n C hC.2.1 j hj] at hi
      simp [hop] at hi
    have hempty : PEqualNP.TwoColour.twoColour n C colour = ∅ :=
      Finset.card_eq_zero.mp hT
    have hnone : ¬ PEqualNP.TwoColour.IsTwoColour n C colour j := by
      intro hm
      have hmem : j ∈ PEqualNP.TwoColour.twoColour n C colour :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hm⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    cases hci : colour i <;> cases hck : colour k
    · rfl
    · exact False.elim (hnone ⟨hj,hor,⟨i,hi,hci⟩,⟨k,hk,hck⟩⟩)
    · exact False.elim (hnone ⟨hj,hor,⟨k,hk,hck⟩,⟨i,hi,hci⟩⟩)
    · rfl

def operand (C : Circuit) (j : ℕ) (s : Fin 2) : ℕ :=
  (gateAt C j).inputs.getD s 0

lemma operand_mem {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (s : Fin 2) :
    operand C j s ∈ (gateAt C j).inputs := by
  have heq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [heq]
    exact hC.2.2 _ (List.getElem_mem hj)
  have hs : s.val < (gateAt C j).inputs.length := by simpa [hlen] using s.isLt
  simp [operand,List.getD,hs]

lemma operand_lt {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (s : Fin 2) :
    operand C j s < n + j :=
  hC.2.1 j hj _ (operand_mem C hC j hj s)

lemma separating_indexed_slot {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x y : Fin n → Bool) (i : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hx : W n C.gates w x) (hy : ¬ W n C.gates w y)
    (hunique : ∀ k, x k = true → y k = false → k = i)
    (hsingle : ¬ W n C.gates w (fun k => decide (k = i))) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ s : Fin 2, operand C j s < n+j ∧
        i ∈ orIn n C (operand C j s) ∧ ¬ W n C.gates (operand C j s) y := by
  obtain ⟨j,hj,hop,z,hzm,hi,hfalse⟩ := separating_slot C hC x y i w hw hx hy hunique hsingle
  obtain ⟨k,hk,hkz⟩ := List.getElem_of_mem hzm
  have heq : gateAt C j = C.gates[j] := by simp [gateAt,List.getD,hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [heq]
    exact hC.2.2 _ (List.getElem_mem hj)
  let s : Fin 2 := ⟨k,by omega⟩
  have hs : operand C j s = z := by simp [operand,List.getD,s,hk,hkz]
  refine ⟨j,hj,hop,s,operand_lt C hC j hj s,?_,?_⟩
  · simpa [hs] using hi
  · simpa [hs] using hfalse

end SeparatingTrace

namespace BipartiteTraces

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SeparatingTrace

def edgeInput {p l : ℕ} (a : Fin p) (b : Fin l) : Fin (p + l) → Bool :=
  Fin.addCases (fun a' => decide (a' = a)) (fun b' => decide (b' = b))

def lineBaseline {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    Fin (p + l) → Bool :=
  Fin.addCases (fun a' => decide (a' = a)) (fun b' => decide ((a, b') ∉ E))

def pointBaseline {p l : ℕ} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    Fin (p + l) → Bool :=
  Fin.addCases (fun a' => decide ((a', b) ∉ E)) (fun b' => decide (b' = b))

lemma opposite_ne {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
  have ha := a.isLt
  omega

lemma output_valid_of_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : W n C.gates C.output x) : C.output < n + C.gates.length := by
  by_contra hn
  have hlen := length_fold C.gates (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  unfold W at hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hx
  contradiction

lemma singleton_output_false {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (i : Fin (p + l)) :
    ¬ W (p + l) C.gates C.output (fun k => decide (k = i)) := by
  intro h
  change circuitFun (p + l) C (fun k => decide (k = i)) = true at h
  rw [hc] at h
  obtain ⟨a, b, _, ha, hb⟩ := of_decide_eq_true h
  have ha' : Fin.castAdd l a = i := of_decide_eq_true ha
  have hb' : Fin.natAdd p b = i := of_decide_eq_true hb
  exact opposite_ne a b (ha'.trans hb'.symm)

lemma edge_output_true {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    W (p + l) C.gates C.output (edgeInput a b) := by
  change circuitFun (p + l) C (edgeInput a b) = true
  rw [hc]
  apply decide_eq_true
  exact ⟨a, b, hab, by simp [edgeInput], by simp [edgeInput]⟩

lemma line_baseline_output_false {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) : ¬ W (p + l) C.gates C.output (lineBaseline E a) := by
  intro h
  change circuitFun (p + l) C (lineBaseline E a) = true at h
  rw [hc] at h
  obtain ⟨a', b', hab, ha, hb⟩ := of_decide_eq_true h
  have he : a' = a := by simpa [lineBaseline] using ha
  subst a'
  have hn : (a, b') ∉ E := by simpa [lineBaseline] using hb
  exact hn hab

lemma point_baseline_output_false {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (b : Fin l) : ¬ W (p + l) C.gates C.output (pointBaseline E b) := by
  intro h
  change circuitFun (p + l) C (pointBaseline E b) = true at h
  rw [hc] at h
  obtain ⟨a', b', hab, ha, hb⟩ := of_decide_eq_true h
  have he : b' = b := by simpa [pointBaseline] using hb
  subst b'
  have hn : (a', b) ∉ E := by simpa [pointBaseline] using ha
  exact hn hab

lemma line_difference_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l) : ∀ k : Fin (p + l),
    edgeInput a b k = true → lineBaseline E a k = false → k = Fin.natAdd p b := by
  intro k hx hy
  induction k using Fin.addCases with
  | left a' =>
      have he : lineBaseline E a (Fin.castAdd l a') = edgeInput a b (Fin.castAdd l a') := by
        simp [lineBaseline, edgeInput]
      rw [he, hx] at hy
      contradiction
  | right b' =>
      have he : b' = b := by simpa [edgeInput] using hx
      exact congrArg (Fin.natAdd p) he

lemma point_difference_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (a : Fin p) (b : Fin l) : ∀ k : Fin (p + l),
    edgeInput a b k = true → pointBaseline E b k = false → k = Fin.castAdd l a := by
  intro k hx hy
  induction k using Fin.addCases with
  | left a' =>
      have he : a' = a := by simpa [edgeInput] using hx
      exact congrArg (Fin.castAdd l) he
  | right b' =>
      have he : pointBaseline E b (Fin.natAdd p b') = edgeInput a b (Fin.natAdd p b') := by
        simp [pointBaseline, edgeInput]
      rw [he, hx] at hy
      contradiction

lemma line_trace {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ z ∈ (gateAt C j).inputs,
        Fin.natAdd p b ∈ orIn (p + l) C z ∧
        ∀ b' : Fin l, Fin.natAdd p b' ∈ orIn (p + l) C z → (a, b') ∈ E := by
  have hx := edge_output_true E C hc a b hab
  have hw := output_valid_of_true C _ hx
  obtain ⟨j, hj, hop, z, hz, hr, hneg⟩ := separating_slot C hC
    (edgeInput a b) (lineBaseline E a) (Fin.natAdd p b) C.output hw hx
    (line_baseline_output_false E C hc a) (line_difference_unique E a b)
    (singleton_output_false E C hc (Fin.natAdd p b))
  refine ⟨j, hj, hop, z, hz, hr, ?_⟩
  intro b' hb'
  have hzlt : z < p + l + C.gates.length := by
    have hh := hC.2.1 j hj z hz
    omega
  have hh := slot_members_false C hC (lineBaseline E a) z hzlt hneg (Fin.natAdd p b') hb'
  simpa [lineBaseline] using hh

lemma point_trace {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ z ∈ (gateAt C j).inputs,
        Fin.castAdd l a ∈ orIn (p + l) C z ∧
        ∀ a' : Fin p, Fin.castAdd l a' ∈ orIn (p + l) C z → (a', b) ∈ E := by
  have hx := edge_output_true E C hc a b hab
  have hw := output_valid_of_true C _ hx
  obtain ⟨j, hj, hop, z, hz, hr, hneg⟩ := separating_slot C hC
    (edgeInput a b) (pointBaseline E b) (Fin.castAdd l a) C.output hw hx
    (point_baseline_output_false E C hc b) (point_difference_unique E a b)
    (singleton_output_false E C hc (Fin.castAdd l a))
  refine ⟨j, hj, hop, z, hz, hr, ?_⟩
  intro a' ha'
  have hzlt : z < p + l + C.gates.length := by
    have hh := hC.2.1 j hj z hz
    omega
  have hh := slot_members_false C hC (pointBaseline E b) z hzlt hneg (Fin.castAdd l a') ha'
  simpa [pointBaseline] using hh


lemma index_and_operand {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (R : ℕ → Prop)
    (h : ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      ∃ z ∈ (gateAt C j).inputs, R z) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧ ∃ s : Fin 2, R (operand C j s) := by
  obtain ⟨j, hj, hop, z, hzm, hz⟩ := h
  obtain ⟨k, hk, hkz⟩ := List.getElem_of_mem hzm
  have heq : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, hj]
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [heq]
    exact hC.2.2 _ (List.getElem_mem hj)
  let slot : Fin 2 := ⟨k, by omega⟩
  have hs : operand C j slot = z := by simp [operand, List.getD, slot, hk, hkz]
  exact ⟨j, hj, hop, slot, hs.symm ▸ hz⟩

lemma line_indexed_trace {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧ ∃ s : Fin 2,
      Fin.natAdd p b ∈ orIn (p + l) C (operand C j s) ∧
      ∀ b' : Fin l, Fin.natAdd p b' ∈ orIn (p + l) C (operand C j s) → (a, b') ∈ E := by
  exact index_and_operand C hC _ (line_trace E C hC hc a b hab)

lemma point_indexed_trace {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hc : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (a : Fin p) (b : Fin l) (hab : (a, b) ∈ E) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧ ∃ s : Fin 2,
      Fin.castAdd l a ∈ orIn (p + l) C (operand C j s) ∧
      ∀ a' : Fin p, Fin.castAdd l a' ∈ orIn (p + l) C (operand C j s) → (a', b) ∈ E := by
  exact index_and_operand C hC _ (point_trace E C hC hc a b hab)

end BipartiteTraces

namespace H4Konig

lemma side {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (P : Finset α) (Q : Finset β)
    (hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card)
    (hcov : ∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) :
    ∃ f : {p // p ∈ P} → β, Function.Injective f ∧ ∀ p, (p.val, f p) ∈ E ∧ f p ∉ Q := by
  let t : {p // p ∈ P} → Finset β :=
    fun p => ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
  have hall : ∀ S : Finset {p // p ∈ P}, S.card ≤ (S.biUnion t).card := by
    intro S
    have hsub : S.image Subtype.val ⊆ P := by
      intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact p.property
    have hc := hmin (P \ S.image Subtype.val) (Q ∪ S.biUnion t) (by
      intro e he
      rcases hcov e he with h | h
      · by_cases hS : e.1 ∈ S.image Subtype.val
        · right
          by_cases hq : e.2 ∈ Q
          · exact Finset.mem_union_left _ hq
          · apply Finset.mem_union_right
            obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hS
            rw [Finset.mem_biUnion]
            refine ⟨p, hp, ?_⟩
            show e.2 ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q
            rw [Finset.mem_sdiff]
            exact ⟨Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hpe.symm⟩, rfl⟩, hq⟩
        · left
          exact Finset.mem_sdiff.mpr ⟨h, hS⟩
      · right
        exact Finset.mem_union_left _ h)
    have h1 : (P \ S.image Subtype.val).card + (S.image Subtype.val).card = P.card :=
      Finset.card_sdiff_add_card_eq_card hsub
    have h2 : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have h3 := Finset.card_union_le Q (S.biUnion t)
    omega
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨f, hinj, fun p => ?_⟩
  have := hf p
  have h' : f p ∈ ((E.filter (fun e => e.1 = p.val)).image Prod.snd) \ Q := this
  rw [Finset.mem_sdiff] at h'
  obtain ⟨e, he, hef⟩ := Finset.mem_image.mp h'.1
  obtain ⟨heE, hep⟩ := Finset.mem_filter.mp he
  refine ⟨?_, h'.2⟩
  have : e = (p.val, f p) := Prod.ext hep hef
  rw [← this]
  exact heE

lemma konig {α β : Type} [DecidableEq α] [DecidableEq β] (E : Finset (α × β)) :
    ∃ (M : Finset (α × β)) (P : Finset α) (Q : Finset β), M ⊆ E ∧
      (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧ (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') ∧
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card ≤ M.card := by
  classical
  have hex : ∃ k : ℕ, ∃ (P : Finset α) (Q : Finset β),
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ Q) ∧ P.card + Q.card = k :=
    ⟨_, E.image Prod.fst, ∅, fun e he => Or.inl (Finset.mem_image_of_mem _ he), rfl⟩
  obtain ⟨P, Q, hcov, hk⟩ := Nat.find_spec hex
  have hmin : ∀ (P' : Finset α) (Q' : Finset β), (∀ e ∈ E, e.1 ∈ P' ∨ e.2 ∈ Q') →
      P.card + Q.card ≤ P'.card + Q'.card := by
    intro P' Q' h
    rw [hk]
    exact Nat.find_min' hex ⟨P', Q', h, rfl⟩
  obtain ⟨f, hfi, hf⟩ := side E P Q hmin hcov
  have hswap : ∀ (a : α) (b : β), (b, a) ∈ E.image Prod.swap ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · intro h
      obtain ⟨e, he, hab⟩ := Finset.mem_image.mp h
      have : e = (a, b) := by
        rw [← Prod.swap_swap e, hab]; rfl
      rw [← this]; exact he
    · intro h
      exact Finset.mem_image.mpr ⟨(a, b), h, rfl⟩
  obtain ⟨g, hgi, hg⟩ := side (E.image Prod.swap) Q P (by
      intro Q' P' h
      have := hmin P' Q' (fun e he => by
        have := h (e.2, e.1) ((hswap e.1 e.2).mpr he)
        exact this.symm)
      omega) (by
      intro e he
      have h1 : (e.2, e.1) ∈ E := (hswap e.2 e.1).mp he
      exact (hcov _ h1).symm)
  have hg' : ∀ q : {q // q ∈ Q}, (g q, q.val) ∈ E ∧ g q ∉ P :=
    fun q => ⟨(hswap _ _).mp (hg q).1, (hg q).2⟩
  let M1 : Finset (α × β) := P.attach.image (fun p => (p.val, f p))
  let M2 : Finset (α × β) := Q.attach.image (fun q => (g q, q.val))
  have m1 : ∀ e ∈ M1, ∃ p : {p // p ∈ P}, e = (p.val, f p) := by
    intro e he
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
    exact ⟨p, hp.symm⟩
  have m2 : ∀ e ∈ M2, ∃ q : {q // q ∈ Q}, e = (g q, q.val) := by
    intro e he
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
    exact ⟨q, hq.symm⟩
  refine ⟨M1 ∪ M2, P, Q, ?_, ?_, ?_, hcov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨p, rfl⟩ := m1 e h
      exact (hf p).1
    · obtain ⟨q, rfl⟩ := m2 e h
      exact (hg' q).1
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := Subtype.ext h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hg' q).2
      have h' : p.val = g q := h
      rw [← h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hg' q).2
      have h' : g q = p.val := h
      rw [h']
      exact p.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := hgi h
      rw [this]
  · intro e he e' he' h
    rcases Finset.mem_union.mp he with h1 | h1 <;> rcases Finset.mem_union.mp he' with h2 | h2
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨p', rfl⟩ := m1 e' h2
      have : p = p' := hfi h
      rw [this]
    · obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, rfl⟩ := m2 e' h2
      exfalso
      apply (hf p).2
      have h' : f p = q.val := h
      rw [h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨p, rfl⟩ := m1 e' h2
      exfalso
      apply (hf p).2
      have h' : q.val = f p := h
      rw [← h']
      exact q.property
    · obtain ⟨q, rfl⟩ := m2 e h1
      obtain ⟨q', rfl⟩ := m2 e' h2
      have : q = q' := Subtype.ext h
      rw [this]
  · have hd : Disjoint M1 M2 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      obtain ⟨p, rfl⟩ := m1 e h1
      obtain ⟨q, hq⟩ := m2 _ h2
      apply (hg' q).2
      have h' : p.val = g q := congrArg Prod.fst hq
      rw [← h']
      exact p.property
    have c1 : M1.card = P.card := by
      rw [Finset.card_image_of_injective _ (fun p p' h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_attach]
    have c2 : M2.card = Q.card := by
      rw [Finset.card_image_of_injective _ (fun q q' h => Subtype.ext (congrArg Prod.snd h)),
        Finset.card_attach]
    rw [Finset.card_union_of_disjoint hd, c1, c2]

end H4Konig

namespace AndBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SeparatingTrace

noncomputable def andSet (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j => (gateAt C j).op = .and

lemma mem_andSet (C : Circuit) (j : ℕ) :
    j ∈ andSet C ↔ j < C.gates.length ∧ (gateAt C j).op = .and := by
  classical
  simp [andSet]

lemma matching_card_le_and_count {p l : ℕ}
    (E M : Finset (Fin p × Fin l)) (C : Circuit)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hC : IsAO2 (p+l) C)
    (hc : ∀ x : Fin (p+l) → Bool,
      circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    M.card ≤ (andSet C).card := by
  classical
  let κ := {j // j ∈ andSet C}
  let P : (κ × Fin 2) → Finset (Fin p) := fun s =>
    Finset.univ.filter fun a => Fin.castAdd l a ∈
      orIn (p+l) C (operand C s.1.val s.2)
  let Q : (κ × Fin 2) → Finset (Fin l) := fun s =>
    Finset.univ.filter fun b => Fin.natAdd p b ∈
      orIn (p+l) C (operand C s.1.val s.2)
  have hmono : ∀ s, P s = ∅ ∨ Q s = ∅ := by
    intro s
    by_contra hn
    have hp : (P s).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inl h))
    have hq : (Q s).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inr h))
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    have hj := ((mem_andSet C s.1.val).mp s.1.property).1
    have hw : operand C s.1.val s.2 < p+l+C.gates.length :=
      (operand_lt C hC s.1.val hj s.2).trans (Nat.add_lt_add_left hj (p+l))
    have heq := orIn_colour_equal C hC (fun i => decide (p ≤ i)) hT
      (operand C s.1.val s.2) hw (Fin.castAdd l a) (Fin.natAdd p b)
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hpa : ¬ p ≤ a.val := Nat.not_le_of_lt a.isLt
    simp [hpa] at heq
  have hp : ∀ e ∈ M, ∃ s, e.1 ∈ P s ∧ ∀ a ∈ P s, (a,e.2) ∈ E := by
    intro e he
    obtain ⟨j,hj,hop,s,ha,hrow⟩ :=
      BipartiteTraces.point_indexed_trace E C hC hc e.1 e.2 (hME he)
    have hjA : j ∈ andSet C := (mem_andSet C j).mpr ⟨hj,hop⟩
    refine ⟨(⟨j,hjA⟩,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,?_⟩
    intro a ha
    exact hrow a (Finset.mem_filter.mp ha).2
  have hq : ∀ e ∈ M, ∃ s, e.2 ∈ Q s ∧ ∀ b ∈ Q s, (e.1,b) ∈ E := by
    intro e he
    obtain ⟨j,hj,hop,s,hb,hcol⟩ :=
      BipartiteTraces.line_indexed_trace E C hC hc e.1 e.2 (hME he)
    have hjA : j ∈ andSet C := (mem_andSet C j).mpr ⟨hj,hop⟩
    refine ⟨(⟨j,hjA⟩,s),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,?_⟩
    intro b hb
    exact hcol b (Finset.mem_filter.mp hb).2
  have hh := H4SlotCount.and_gate_matching_bound E M hleft hright hc4 P Q hmono hp hq
  simpa only [κ, Fintype.card_coe] using hh

lemma exists_cover_le_and_count {p l : ℕ}
    (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hC : IsAO2 (p+l) C)
    (hc : ∀ x : Fin (p+l) → Bool,
      circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0) :
    ∃ S : Finset (Fin (p+l)),
      (∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ (andSet C).card := by
  classical
  obtain ⟨M,P,Q,hME,hleft,hright,hcov,hcard⟩ := H4Konig.konig E
  have hM := matching_card_le_and_count E M C hc4 hC hc hT hME hleft hright
  refine ⟨P.image (Fin.castAdd l) ∪ Q.image (Fin.natAdd p),?_,?_⟩
  · intro a b hab
    rcases hcov (a,b) hab with ha | hb
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb))
  · have hU := Finset.card_union_le (P.image (Fin.castAdd l)) (Q.image (Fin.natAdd p))
    have hP := Finset.card_image_le (f := Fin.castAdd l) (s := P)
    have hQ := Finset.card_image_le (f := Fin.natAdd p) (s := Q)
    omega

end AndBound


namespace SlotSurplus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4970.SeparatingTrace
open PEqualNP.Outside.L_meta_4970.AndBound

abbrev Slots (C : Circuit) := {j // j ∈ andSet C} × Fin 2

def wire (C : Circuit) (s : Slots C) : ℕ := operand C s.1.val s.2

noncomputable def emptySlots (n : ℕ) (C : Circuit) : Finset (Slots C) := by
  classical
  exact Finset.univ.filter fun s => orIn n C (wire C s) = ∅

noncomputable def directAndSlots (n : ℕ) (C : Circuit) : Finset (Slots C) := by
  classical
  exact Finset.univ.filter fun s => ∃ j ∈ andSet C, wire C s = n + j

lemma matching_slot_surplus {p l : ℕ}
    (E M : Finset (Fin p × Fin l)) (C : Circuit)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hC : IsAO2 (p+l) C)
    (hc : ∀ x : Fin (p+l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) :
    2 * M.card + (emptySlots (p+l) C).card ≤ 2 * (andSet C).card := by
  classical
  let active : Finset (Slots C) := Finset.univ \ emptySlots (p+l) C
  let σ := {s // s ∈ active}
  let P : σ → Finset (Fin p) := fun s =>
    Finset.univ.filter fun a => Fin.castAdd l a ∈ orIn (p+l) C (wire C s.val)
  let Q : σ → Finset (Fin l) := fun s =>
    Finset.univ.filter fun b => Fin.natAdd p b ∈ orIn (p+l) C (wire C s.val)
  have hmono : ∀ s, P s = ∅ ∨ Q s = ∅ := by
    intro s
    by_contra hn
    have hp : (P s).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inl h))
    have hq : (Q s).Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hn (Or.inr h))
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    have hj := ((mem_andSet C s.val.1.val).mp s.val.1.property).1
    have hw : wire C s.val < p+l+C.gates.length :=
      (operand_lt C hC s.val.1.val hj s.val.2).trans (Nat.add_lt_add_left hj (p+l))
    have heq := orIn_colour_equal C hC (fun i => decide (p ≤ i)) hT
      (wire C s.val) hw (Fin.castAdd l a) (Fin.natAdd p b)
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
    have hpa : ¬ p ≤ a.val := Nat.not_le_of_lt a.isLt
    simp [hpa] at heq
  have hp : ∀ e ∈ M, ∃ s : σ, e.1 ∈ P s ∧ ∀ a ∈ P s, (a,e.2) ∈ E := by
    intro e he
    obtain ⟨j,hj,hop,k,ha,hrow⟩ :=
      BipartiteTraces.point_indexed_trace E C hC hc e.1 e.2 (hME he)
    let s : Slots C := (⟨j,(mem_andSet C j).mpr ⟨hj,hop⟩⟩,k)
    have hnonempty : orIn (p+l) C (wire C s) ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨Fin.castAdd l e.1,ha⟩
    have hs : s ∈ active := by simp [active,emptySlots,hnonempty]
    refine ⟨⟨s,hs⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩,?_⟩
    intro a ha
    exact hrow a (Finset.mem_filter.mp ha).2
  have hq : ∀ e ∈ M, ∃ s : σ, e.2 ∈ Q s ∧ ∀ b ∈ Q s, (e.1,b) ∈ E := by
    intro e he
    obtain ⟨j,hj,hop,k,hb,hcol⟩ :=
      BipartiteTraces.line_indexed_trace E C hC hc e.1 e.2 (hME he)
    let s : Slots C := (⟨j,(mem_andSet C j).mpr ⟨hj,hop⟩⟩,k)
    have hnonempty : orIn (p+l) C (wire C s) ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨Fin.natAdd p e.2,hb⟩
    have hs : s ∈ active := by simp [active,emptySlots,hnonempty]
    refine ⟨⟨s,hs⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,?_⟩
    intro b hb
    exact hcol b (Finset.mem_filter.mp hb).2
  let pointSlot : {e // e ∈ M} → σ := fun e => Classical.choose (hp e.val e.property)
  let lineSlot : {e // e ∈ M} → σ := fun e => Classical.choose (hq e.val e.property)
  have hbound := H4SlotCount.two_colour_slot_bound E M hleft hright hc4 P Q hmono
    pointSlot lineSlot (fun e => Classical.choose_spec (hp e.val e.property))
    (fun e => Classical.choose_spec (hq e.val e.property))
  have hactive : 2 * M.card ≤ active.card := by
    simpa only [σ,Fintype.card_coe] using hbound
  have hsum := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (emptySlots (p+l) C))
  change active.card + (emptySlots (p+l) C).card = (Finset.univ : Finset (Slots C)).card at hsum
  have htotal : (Finset.univ : Finset (Slots C)).card = 2 * (andSet C).card := by
    simp [Slots,Fintype.card_prod,Nat.mul_comm]
  omega

lemma directAndSlots_subset_emptySlots {n : ℕ} (C : Circuit) (hC : IsAO2 n C) :
    directAndSlots n C ⊆ emptySlots n C := by
  classical
  intro s hs
  obtain ⟨_,j,hj,hw⟩ := Finset.mem_filter.mp hs
  obtain ⟨hjl,hop⟩ := (mem_andSet C j).mp hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  rw [hw,orIn_gate n C hC.2.1 j hjl]
  simp [hop]

lemma directAndSlots_card_le {n m : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (h : 2 * m + (emptySlots n C).card ≤ 2 * (andSet C).card) :
    (directAndSlots n C).card ≤ 2 * ((andSet C).card - m) := by
  have hsub := Finset.card_le_card (directAndSlots_subset_emptySlots C hC)
  omega

lemma operand_raw_nonempty_of_emptySlots_eq_empty {n : ℕ} (C : Circuit)
    (hempty : emptySlots n C = ∅) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) (s : Fin 2) :
    (orIn n C (operand C j s)).Nonempty := by
  classical
  by_contra hn
  have hz : orIn n C (operand C j s) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  let slot : Slots C := (⟨j,(mem_andSet C j).mpr ⟨hj,hop⟩⟩,s)
  have hm : slot ∈ emptySlots n C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
  rw [hempty] at hm
  exact Finset.notMem_empty _ hm

lemma emptySlots_zero_of_tight {p l : ℕ}
    (E M : Finset (Fin p × Fin l)) (C : Circuit)
    (hc4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hC : IsAO2 (p+l) C)
    (hc : ∀ x : Fin (p+l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p+l) C x = decide (∃ a b, (a,b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hT : PEqualNP.TwoColour.tCount (p+l) C (fun i => decide (p ≤ i)) = 0)
    (hME : M ⊆ E)
    (hleft : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hright : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (htight : (andSet C).card = M.card) :
    emptySlots (p+l) C = ∅ := by
  have h := matching_slot_surplus E M C hc4 hC hc hT hME hleft hright
  apply Finset.card_eq_zero.mp
  omega

end SlotSurplus

end PEqualNP.Outside.L_meta_4970
