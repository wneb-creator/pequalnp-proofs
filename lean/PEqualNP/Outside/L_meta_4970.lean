import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.H4OrBlock

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

end PEqualNP.Outside.L_meta_4970.H4OrBlock

namespace PEqualNP.Outside.L_meta_4970.SafeBirth

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

end PEqualNP.Outside.L_meta_4970.SafeBirth

namespace PEqualNP.Outside.L_meta_4970.BirthObstruction

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

lemma birth_gate_is_unsafe :
    value 2 (pair 1 0) = true ∧ circuitFun 4 circuit (pair 1 0) = false := by
  decide +kernel

lemma size_six : circuit.size = 6 := by
  rfl

end PEqualNP.Outside.L_meta_4970.BirthObstruction
