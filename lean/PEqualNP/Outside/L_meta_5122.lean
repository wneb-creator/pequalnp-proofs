import PEqualNP.Defs
-- Circuit reachability and the large-set charge are adapted from e62575df in accepted PR 8876.
namespace PEqualNP.Outside.L_meta_5122_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.EdgeOwnership
lemma zsplit_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


lemma zgateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma zorFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma zorStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma zorStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma zorFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact zorStep_getD_lt n cs g k hk

lemma zorSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := zsplit_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [zgateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [zorFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, zorFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, zorFold_getD_lt n post _ m (by omega)]
    exact zorStep_getD_lt n _ gk m (by omega)
  have h3 := zorStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma zqorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [zorFold_length]
  simp

lemma zqreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (zorSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (zorSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma zqreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [zqorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma zqreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (zqreach_iff n C k k hk).2 (Or.inl rfl)

lemma zqmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma zqorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (zqmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := zqreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (zqreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma zqorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := zqorIn_eq_self n C w hw a ha
  have h2 := zqorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma zqorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, zqmem_orIn, zqmem_orIn, zqmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (zqreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, zqreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (zqreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

lemma fin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [zgateAt_eq C j hj]; exact List.getElem_mem hj

lemma inputs_eq {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have h := hC.2.2 (gateAt C j) (gateAt_mem hj)
  unfold opnd
  generalize (gateAt C j).inputs = l at h ⊢
  match l, h with
  | [a, b], _ => rfl

lemma opnd_mem {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (i : Fin 2) : opnd C j i ∈ (gateAt C j).inputs := by
  rw [inputs_eq hC hj]
  rcases fin2 i with rfl | rfl <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (i : Fin 2) : opnd C j i < n + j := hC.2.1 j hj _ (opnd_mem hC hj i)

lemma orIn_or {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) :=
  zqorIn_or n C j _ _ hj hop (inputs_eq hC hj) (opnd_lt hC hj 0) (opnd_lt hC hj 1)

lemma orIn_sub {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (i : Fin 2) :
    orIn n C (opnd C j i) ⊆ orIn n C (n + j) := by
  rw [orIn_or hC hj hop]
  rcases fin2 i with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma orIn_split {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) {y : Fin n} (hy : y ∈ orIn n C (n + j)) :
    ∃ i : Fin 2, y ∈ orIn n C (opnd C j i) := by
  rw [orIn_or hC hj hop, Finset.mem_union] at hy
  rcases hy with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

def C4free {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b x y : Fin n, a ≠ b → x ≠ y → G.Adj a x → G.Adj a y → G.Adj b x → G.Adj b y → False

section comb
open Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}

noncomputable def sm {α : Type} (k : ℕ) (A : Finset α) : Finset α := if A.card ≤ k then A else ∅

lemma sm_card {α : Type} {k : ℕ} {A : Finset α} : (sm k A).card ≤ k := by
  unfold sm
  split_ifs with h
  · exact h
  · simp

lemma mem_sm {α : Type} {k : ℕ} {A : Finset α} {x : α} (h : A.card ≤ k) (hx : x ∈ A) :
    x ∈ sm k A := by
  unfold sm
  rw [if_pos h]
  exact hx

lemma bi2_card {α : Type} [DecidableEq α] (f : Fin 2 → Finset α) (k : ℕ) (h : ∀ i, (f i).card ≤ k) :
    ((Finset.univ : Finset (Fin 2)).biUnion f).card ≤ 2 * k := by
  have := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 2)) f k (fun i _ => h i)
  simpa using this

lemma img_card (A B : Finset (Fin n)) (a b : ℕ) (hA : A.card ≤ a) (hB : B.card ≤ b) :
    ((A ×ˢ B).image fun p => s(p.1, p.2)).card ≤ a * b := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  exact Nat.mul_le_mul hA hB

lemma uniq_cn (h4 : C4free G) (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
    (Finset.univ.filter fun z => ∀ x ∈ A, G.Adj z x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  rw [Finset.mem_filter] at hz hz'
  by_contra hne
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hA
  exact h4 z z' x y hne hxy (hz.2 x hx) (hz.2 y hy) (hz'.2 x hx) (hz'.2 y hy)

lemma uniq_kappa (h4 : C4free G) (A : Finset (Fin n)) (hA : 4 ≤ A.card) :
    (Finset.univ.filter fun z => (A.filter fun x => ¬ G.Adj z x).card ≤ 1).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  rw [Finset.mem_filter] at hz hz'
  by_contra hne
  have h1 := Finset.le_card_sdiff
    ((A.filter fun x => ¬ G.Adj z x) ∪ (A.filter fun x => ¬ G.Adj z' x)) A
  have h2 := Finset.card_union_le (A.filter fun x => ¬ G.Adj z x)
    (A.filter fun x => ¬ G.Adj z' x)
  have h3 : 1 < (A \ ((A.filter fun x => ¬ G.Adj z x) ∪
      (A.filter fun x => ¬ G.Adj z' x))).card := by
    have := hz.2
    have := hz'.2
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h3
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, not_or, not_and,
    not_not] at hx hy
  exact h4 z z' x y hne hxy (hx.2.1 hx.1) (hy.2.1 hy.1) (hx.2.2 hx.1) (hy.2.2 hy.1)

lemma descK (hC : IsAO2 n C) (z y : Fin n) :
    ∀ w, y ∈ orIn n C w → 4 ≤ (orIn n C w).card →
      ((orIn n C w).filter fun x => ¬ G.Adj z x).card ≤ 1 →
      ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ 4 ≤ (orIn n C (n + g)).card ∧
        ((orIn n C (n + g)).filter fun x => ¬ G.Adj z x).card ≤ 1 ∧
        ∃ i : Fin 2, y ∈ orIn n C (opnd C g i) ∧ (orIn n C (opnd C g i)).card ≤ 3 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hy hbig ht
    by_cases hw : n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or
    · obtain ⟨h1, h2, hop⟩ := hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have e : n + k - n = k := by omega
      rw [e] at h2 hop
      obtain ⟨i, hi⟩ := orIn_split hC h2 hop hy
      by_cases hs : (orIn n C (opnd C k i)).card ≤ 3
      · exact ⟨k, h2, hop, hbig, ht, i, hi, hs⟩
      · exact ih _ (opnd_lt hC h2 i) hi (by omega)
          ((Finset.card_le_card (Finset.filter_subset_filter _ (orIn_sub hC h2 hop i))).trans ht)
    · have := zqorIn_small n C w hw
      omega

noncomputable def FK (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Sym2 (Fin n)) :=
  if 4 ≤ (orIn n C (n + g)).card then
    ((Finset.univ.filter fun z => ((orIn n C (n + g)).filter fun x => ¬ G.Adj z x).card ≤ 1) ×ˢ
      ((Finset.univ : Finset (Fin 2)).biUnion fun i => sm 3 (orIn n C (opnd C g i)))).image
        fun p => s(p.1, p.2)
  else ∅

lemma FK_card (h4 : C4free G) (g : ℕ) : (FK G C g).card ≤ 6 := by
  unfold FK
  split_ifs with h
  · have := img_card _ _ 1 6 (uniq_kappa h4 _ h)
      (bi2_card (fun i => sm 3 (orIn n C (opnd C g i))) 3 (fun i => sm_card))
    omega
  · simp

lemma small_centres {A : Finset (Fin n)} (h4 : C4free G) (hA : A.card = 3) :
    (Finset.univ.filter fun z => (A.filter fun x => ¬ G.Adj z x).card ≤ 1).card ≤ 3 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hA
  let both (x y : Fin n) := Finset.univ.filter fun z => G.Adj z x ∧ G.Adj z y
  have pair_bound (x y : Fin n) (hxy : x ≠ y) : (both x y).card ≤ 1 := by
    simpa [both] using uniq_cn (G := G) h4 ({x, y} : Finset _) (by simp [hxy])
  have cover : (Finset.univ.filter fun z =>
      (({a, b, c} : Finset (Fin n)).filter fun x => ¬ G.Adj z x).card ≤ 1) ⊆
      (both a b ∪ both a c) ∪ both b c := by
    intro z hz
    have misses := (Finset.mem_filter.mp hz).2
    simp only [both, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : G.Adj z a <;> by_cases hb : G.Adj z b <;> by_cases hc : G.Adj z c <;>
      simp_all [Finset.filter_insert]
  have habound := Finset.card_union_le (both a b) (both a c)
  have hbound := Finset.card_union_le (both a b ∪ both a c) (both b c)
  have hp := Finset.card_le_card cover
  have hp1 := pair_bound a b hab
  have hp2 := pair_bound a c hac
  have hp3 := pair_bound b c hbc
  omega

noncomputable def smallEdges (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if A.card = 3 then
    ((Finset.univ.filter fun z => (A.filter fun x => ¬ G.Adj z x).card ≤ 1) ×ˢ A).image
      fun p => s(p.1,p.2)
  else if A.card = 2 then
    ((Finset.univ.filter fun z => ∀ x ∈ A, G.Adj z x) ×ˢ A).image fun p => s(p.1,p.2)
  else ∅

lemma smallEdges_card (h4 : C4free G) (A : Finset (Fin n)) : (smallEdges G A).card ≤ 12 := by
  unfold smallEdges
  split_ifs with h3 h2
  · exact (img_card _ _ 3 3 (small_centres h4 h3) (by omega)).trans (by decide)
  · exact (img_card _ _ 1 2 (uniq_cn h4 A (by omega)) (by omega)).trans (by decide)
  · simp

noncomputable def wireCharge (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Finset (Sym2 (Fin n)) :=
  if 4 ≤ (orIn n C (n + g)).card then FK G C g else smallEdges G (orIn n C (n + g))

lemma wireCharge_card (h4 : C4free G) (g : ℕ) : (wireCharge G C g).card ≤ 12 := by
  unfold wireCharge
  split_ifs
  · exact (FK_card h4 g).trans (by decide)
  · exact smallEdges_card h4 _

lemma placePair (hC : IsAO2 n C) (z y : Fin n) (w : ℕ) (hw : w < n + C.gates.length)
    (hy : y ∈ orIn n C w)
    (H : (2 ≤ (orIn n C w).card ∧ ∀ x ∈ orIn n C w, G.Adj z x) ∨
      3 ≤ (orIn n C w).card ∧ ((orIn n C w).filter fun x => ¬ G.Adj z x).card ≤ 1) :
    ∃ g < C.gates.length, s(z,y) ∈ wireCharge G C g := by
  have h2 : 2 ≤ (orIn n C w).card := by rcases H with h | h <;> omega
  have hnear : ((orIn n C w).filter fun x => ¬ G.Adj z x).card ≤ 1 := by
    rcases H with h | h
    · have hempty : ((orIn n C w).filter fun x => ¬ G.Adj z x) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun x hx => not_not_intro (h.2 x hx)
      simp [hempty]
    · exact h.2
  by_cases h4 : 4 ≤ (orIn n C w).card
  · obtain ⟨g, hg, _, big, near, i, hi, hs⟩ := descK hC z y w hy h4 hnear
    refine ⟨g, hg, ?_⟩
    rw [wireCharge, if_pos big, FK, if_pos big]
    exact Finset.mem_image.2 ⟨(z,y), Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, near⟩,
        Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, mem_sm hs hi⟩⟩, rfl⟩
  have hn : n ≤ w := by
    by_contra hn
    have := zqorIn_small n C w (fun h => hn h.1)
    omega
  obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
  refine ⟨g, by omega, ?_⟩
  rw [wireCharge, if_neg h4, smallEdges]
  split_ifs with three two
  · exact Finset.mem_image.2 ⟨(z,y), Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hnear⟩, hy⟩, rfl⟩
  · have hall : ∀ x ∈ orIn n C (n+g), G.Adj z x := by
      rcases H with h | h
      · exact h.2
      · omega
    exact Finset.mem_image.2 ⟨(z,y), Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hall⟩, hy⟩, rfl⟩
  · omega

end comb
end PEqualNP.Outside.L_meta_5122_aux

open PEqualNP.Outside.L_meta_5122_aux
theorem PEqualNP.Outside.L_meta_5122 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x5 → ∀ (x7 : Finset (Sym2 (Fin x1))), (∀ x8 ∈ x7, ∃ (x10 : Fin x1) (x11 : Fin x1), x8 = s(x10, x11) ∧ ∃ x12 < x1 + x5.gates.length, x11 ∈ PEqualNP.TopForm.orIn x1 x5 x12 ∧ (((2 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x5 x12).card ∧ ∀ x13 ∈ PEqualNP.TopForm.orIn x1 x5 x12, x2.Adj x10 x13) ∨ (3 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x5 x12).card ∧ {x13 ∈ PEqualNP.TopForm.orIn x1 x5 x12 | ¬x2.Adj x10 x13}.card ≤ (1 : ℕ))) → x7.card ≤ (12 : ℕ) * x5.size := by
  intro n G _ hg C hC E hE
  classical
  have h4 : C4free G := by
    intro a b x y hab hxy hax hay hbx hby
    exact no4 G hg a x b y hax hbx.symm hby hay.symm hab hxy
  have hsub : E ⊆ (Finset.range C.gates.length).biUnion (wireCharge G C) := by
    intro e he
    obtain ⟨u, v, rfl, w, hw, hv, H⟩ := hE e he
    obtain ⟨g, hlen, hm⟩ := placePair (G := G) hC u v w hw hv (by
      rcases H with h | ⟨hs, hn⟩
      · exact Or.inl h
      · refine Or.inr ⟨hs, (Finset.card_le_card ?_).trans hn⟩
        intro x hx
        simpa only [Finset.mem_filter] using hx)
    exact Finset.mem_biUnion.2 ⟨g, Finset.mem_range.2 hlen, hm⟩
  have hb := Finset.card_biUnion_le_card_mul (Finset.range C.gates.length) (wireCharge G C) 12
    (fun g _ => wireCharge_card h4 g)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_range] at hb
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
