namespace PEqualNP.Outside.L_meta_1031.CycleElim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1031.ForestAux

def ThreeZero (n : ℕ) (C : Circuit) (u : Fin n) : Prop :=
  ∃ a b c : ℕ, [a, b, c].Nodup ∧
    a < C.gates.length ∧ b < C.gates.length ∧ c < C.gates.length ∧ a < c ∧
    (gateAt C a).op = GateOp.and ∧
    u.val ∈ (gateAt C a).inputs ∧ u.val ∈ (gateAt C b).inputs ∧
    n + a ∈ (gateAt C c).inputs

def FourOneFork (n : ℕ) (C : Circuit) (u : Fin n) : Prop :=
  ∃ a b c d : ℕ, [a, b, c, d].Nodup ∧
    a < C.gates.length ∧ b < C.gates.length ∧ c < C.gates.length ∧
    d < C.gates.length ∧ a < c ∧ b < d ∧
    (gateAt C a).op = GateOp.or ∧ (gateAt C b).op = GateOp.or ∧
    u.val ∈ (gateAt C a).inputs ∧ u.val ∈ (gateAt C b).inputs ∧
    n + a ∈ (gateAt C c).inputs ∧ n + b ∈ (gateAt C d).inputs

def FourOneChain (n : ℕ) (C : Circuit) (u : Fin n) : Prop :=
  ∃ a b c d : ℕ, [a, b, c, d].Nodup ∧
    a < C.gates.length ∧ b < C.gates.length ∧ c < C.gates.length ∧
    d < C.gates.length ∧ a < c ∧ b < c ∧ c < d ∧
    (gateAt C a).op = GateOp.or ∧ (gateAt C b).op = GateOp.or ∧
    u.val ∈ (gateAt C a).inputs ∧ u.val ∈ (gateAt C b).inputs ∧
    n + a ∈ (gateAt C c).inputs ∧ n + b ∈ (gateAt C c).inputs ∧
    n + c ∈ (gateAt C d).inputs

def prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (j : ℕ) :
    List Stat × List Gate := elim n (gs.take j) acc

def skips (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (j : ℕ) : Prop :=
  (simplify (gs.getD j ⟨GateOp.or, []⟩).op (n + (prefix n gs acc j).2.length)
    ((gs.getD j ⟨GateOp.or, []⟩).inputs.map
      fun i => (prefix n gs acc j).1.getD i (Sum.inl false))).1 = none

lemma prefix_succ (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    prefix n gs acc (j + 1) = elimStep n (prefix n gs acc j) gs[j] := by
  simp [prefix, List.take_succ_eq_append_getElem hj, elim, List.foldl_append]

lemma elim_stats_length (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep]
    omega

lemma prefix_stats_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j : ℕ) (hj : j ≤ gs.length) :
    (prefix n gs acc j).1.length = acc.1.length + j := by
  simp [prefix, elim_stats_length, List.length_take, Nat.min_eq_left hj]

lemma skip_count (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.length + ((Finset.range gs.length).filter (skips n gs acc)).card =
      acc.2.length + gs.length := by
  classical
  have step (j : ℕ) (hj : j < gs.length) :
      (prefix n gs acc (j + 1)).2.length + (if skips n gs acc j then 1 else 0) =
        (prefix n gs acc j).2.length + 1 := by
    rw [prefix_succ n gs acc j hj]
    simp only [elimStep, List.length_append]
    have hg : gs.getD j ⟨GateOp.or, []⟩ = gs[j] := List.getD_eq_getElem _ _ hj
    simp only [skips, hg]
    cases he : (simplify gs[j].op (n + (prefix n gs acc j).2.length)
      (gs[j].inputs.map fun i => (prefix n gs acc j).1.getD i (Sum.inl false))).1 <;>
      simp [he]
  have aux : ∀ j, j ≤ gs.length →
      (prefix n gs acc j).2.length + ((Finset.range j).filter (skips n gs acc)).card =
        acc.2.length + j := by
    intro j
    induction j with
    | zero => intro _; simp [prefix, elim]
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hs := step j (by omega)
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hskip : skips n gs acc j
      · simp only [hskip, ite_true] at hs ⊢
        rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · simp only [hskip, ite_false] at hs ⊢
        omega
  simpa [prefix] using aux gs.length (le_refl _)

lemma marked_skips_bound (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < gs.length ∧ skips n gs acc j) :
    (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  classical
  have hsub : S ⊆ (Finset.range gs.length).filter (skips n gs acc) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hS j hj).1, (hS j hj).2⟩
  have hcard := Finset.card_le_card hsub
  have he := skip_count n gs acc
  omega

def initAt (n : ℕ) (u : Fin n) (b : Bool) : List Stat :=
  List.ofFn fun i : Fin n => if i = u then Sum.inl b else Sum.inr i.val

lemma initAt_length (n : ℕ) (u : Fin n) (b : Bool) : (initAt n u b).length = n := by
  simp [initAt]

lemma initAt_fixed (n : ℕ) (u : Fin n) (b : Bool) :
    (initAt n u b).getD u.val (Sum.inl false) = Sum.inl b := by
  simp [initAt]

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma prefix_get (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j : ℕ) (hj : j ≤ gs.length) (i : ℕ) (hi : i < acc.1.length + j) :
    (elim n gs acc).1.getD i (Sum.inl false) =
      (prefix n gs acc j).1.getD i (Sum.inl false) := by
  have hs : elim n gs acc = elim n (gs.drop j) (prefix n gs acc j) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [elim_append]
    rfl
  rw [hs]
  apply elim_getD
  rw [prefix_stats_length n gs acc j hj]
  exact hi

lemma gate_status_next (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    (prefix n gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) =
      (simplify gs[j].op (n + (prefix n gs acc j).2.length)
        (gs[j].inputs.map fun i => (prefix n gs acc j).1.getD i (Sum.inl false))).2 := by
  rw [prefix_succ n gs acc j hj]
  change ((prefix n gs acc j).1 ++ [_]).getD (acc.1.length + j) (Sum.inl false) = _
  exact getD_snoc_len _ _ _ _ (prefix_stats_length n gs acc j (le_of_lt hj))

lemma gate_const_before (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j k : ℕ) (hj : j < k) (hk : k ≤ gs.length) (b : Bool)
    (hc : (simplify gs[j].op (n + (prefix n gs acc j).2.length)
      (gs[j].inputs.map fun i => (prefix n gs acc j).1.getD i (Sum.inl false))).2 =
        Sum.inl b) :
    (prefix n gs acc k).1.getD (acc.1.length + j) (Sum.inl false) = Sum.inl b := by
  have hjl : j < gs.length := by omega
  have hs := gate_status_next n gs acc j hjl
  rw [hc] at hs
  have hf : (elim n gs acc).1.getD (acc.1.length + j) (Sum.inl false) = Sum.inl b := by
    rw [prefix_get n gs acc (j + 1) (by omega) _ (by omega)]
    exact hs
  rw [prefix_get n gs acc k hk _ (by omega)] at hf
  exact hf

lemma prefix_input_const (n : ℕ) (gs : List Gate) (u : Fin n) (b : Bool) (j : ℕ) :
    (prefix n gs (initAt n u b, []) j).1.getD u.val (Sum.inl false) = Sum.inl b := by
  rw [prefix, elim_getD n u.val (Sum.inl false) (gs.take j)
    (initAt n u b, []) (by simpa [initAt] using u.isLt)]
  exact initAt_fixed n u b

lemma const_skips (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (j : ℕ) (hj : j < gs.length) (hok : NOk gs[j]) (i : ℕ)
    (hi : i ∈ gs[j].inputs) (b : Bool)
    (hc : (prefix n gs acc j).1.getD i (Sum.inl false) = Sum.inl b) :
    skips n gs acc j := by
  unfold skips
  rw [List.getD_eq_getElem _ _ hj]
  apply simplify_count
  · exact hok.1.1
  · simpa using hok.1.2
  · intro hn; simpa using hok.2 hn
  · exact ⟨b, List.mem_map.mpr ⟨i, hi, hc⟩⟩

lemma simplify_and_zero (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hc : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpAnd]

lemma simplify_or_one (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hc : Sum.inl true ∈ ins) :
    simplify GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpOr]

lemma mono_nok (C : Circuit) (hC : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    NOk C.gates[j] := by
  obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hj)
  refine ⟨⟨?_, hlen⟩, ?_⟩
  · rcases hop with ha | ho
    · exact Or.inl ha
    · exact Or.inr (Or.inl ho)
  · intro hn
    rcases hop with ha | ho <;> rw [hn] at * <;> contradiction

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  exact List.getD_eq_getElem _ _ hj

lemma input_skips (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n) (b : Bool)
    (j : ℕ) (hj : j < C.gates.length) (hu : u.val ∈ (gateAt C j).inputs) :
    skips n C.gates (initAt n u b, []) j := by
  rw [gateAt_get C j hj] at hu
  exact const_skips n C.gates _ j hj (mono_nok C hC j hj) u.val hu b
    (prefix_input_const n C.gates u b j)

lemma and_input_zero (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (j k : ℕ) (hj : j < k) (hk : k ≤ C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (hu : u.val ∈ (gateAt C j).inputs) :
    (prefix n C.gates (initAt n u false, []) k).1.getD (n + j) (Sum.inl false) =
      Sum.inl false := by
  have hjl : j < C.gates.length := by omega
  rw [gateAt_get C j hjl] at hop hu
  have hn : (initAt n u false).length = n := initAt_length n u false
  have hresult := gate_const_before n C.gates (initAt n u false, []) j k hj hk false
  apply (by simpa only [initAt_length] using hresult)
  have he := simplify_and_zero (n + (prefix n C.gates (initAt n u false, []) j).2.length)
    (C.gates[j].inputs.map fun i =>
      (prefix n C.gates (initAt n u false, []) j).1.getD i (Sum.inl false))
    (by simpa using (hC _ (List.getElem_mem hjl)).2)
    (List.mem_map.mpr ⟨u.val, hu, prefix_input_const n C.gates u false j⟩)
  rw [hop, he]

lemma or_input_one (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (j k : ℕ) (hj : j < k) (hk : k ≤ C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hu : u.val ∈ (gateAt C j).inputs) :
    (prefix n C.gates (initAt n u true, []) k).1.getD (n + j) (Sum.inl false) =
      Sum.inl true := by
  have hjl : j < C.gates.length := by omega
  rw [gateAt_get C j hjl] at hop hu
  have hn : (initAt n u true).length = n := initAt_length n u true
  have hresult := gate_const_before n C.gates (initAt n u true, []) j k hj hk true
  apply (by simpa only [initAt_length] using hresult)
  have he := simplify_or_one (n + (prefix n C.gates (initAt n u true, []) j).2.length)
    (C.gates[j].inputs.map fun i =>
      (prefix n C.gates (initAt n u true, []) j).1.getD i (Sum.inl false))
    (by simpa using (hC _ (List.getElem_mem hjl)).2)
    (List.mem_map.mpr ⟨u.val, hu, prefix_input_const n C.gates u true j⟩)
  rw [hop, he]

lemma three_skips (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (hthree : ThreeZero n C u) :
    (elim n C.gates (initAt n u false, [])).2.length + 3 ≤ C.gates.length := by
  classical
  obtain ⟨a, b, c, hnd, ha, hb, hc, hac, hop, hua, hub, hca⟩ := hthree
  have hsa := input_skips n C hC u false a ha hua
  have hsb := input_skips n C hC u false b hb hub
  have hsc : skips n C.gates (initAt n u false, []) c := by
    rw [gateAt_get C c hc] at hca
    exact const_skips n C.gates _ c hc (mono_nok C hC c hc) (n + a) hca false
      (and_input_zero n C hC u a c hac (le_of_lt hc) hop hua)
  have hh := marked_skips_bound n C.gates (initAt n u false, []) [a, b, c].toFinset (by
    intro j hj
    simp only [List.mem_toFinset, List.mem_cons, List.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact ⟨ha, hsa⟩
    · exact ⟨hb, hsb⟩
    · exact ⟨hc, hsc⟩)
  simpa [List.toFinset_card_of_nodup hnd] using hh

lemma four_fork_skips (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (hfour : FourOneFork n C u) :
    (elim n C.gates (initAt n u true, [])).2.length + 4 ≤ C.gates.length := by
  classical
  obtain ⟨a, b, c, d, hnd, ha, hb, hc, hd, hac, hbd, hoa, hob, hua, hub, hca, hdb⟩ := hfour
  have hsa := input_skips n C hC u true a ha hua
  have hsb := input_skips n C hC u true b hb hub
  have hsc : skips n C.gates (initAt n u true, []) c := by
    rw [gateAt_get C c hc] at hca
    exact const_skips n C.gates _ c hc (mono_nok C hC c hc) (n + a) hca true
      (or_input_one n C hC u a c hac (le_of_lt hc) hoa hua)
  have hsd : skips n C.gates (initAt n u true, []) d := by
    rw [gateAt_get C d hd] at hdb
    exact const_skips n C.gates _ d hd (mono_nok C hC d hd) (n + b) hdb true
      (or_input_one n C hC u b d hbd (le_of_lt hd) hob hub)
  have hh := marked_skips_bound n C.gates (initAt n u true, []) [a, b, c, d].toFinset (by
    intro j hj
    simp only [List.mem_toFinset, List.mem_cons, List.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨ha, hsa⟩
    · exact ⟨hb, hsb⟩
    · exact ⟨hc, hsc⟩
    · exact ⟨hd, hsd⟩)
  simpa [List.toFinset_card_of_nodup hnd] using hh

lemma two_members_cover (L : List ℕ) (hL : L.length ≤ 2) (a b : ℕ) (hab : a ≠ b)
    (ha : a ∈ L) (hb : b ∈ L) : ∀ i ∈ L, i = a ∨ i = b := by
  rcases L with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb
    exact False.elim (hab (ha.trans hb.symm))
  · intro i hi
    simp only [List.mem_cons, List.mem_singleton] at ha hb hi
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hi with hi | hi <;> simp_all
  · simp at hL

lemma simplify_all_one (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2) (hne : ins ≠ [])
    (hall : ∀ s ∈ ins, s = Sum.inl true) :
    simplify op m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact False.elim (hne rfl)
  · have ha := hall a (by simp)
    subst a
    rcases hop with rfl | rfl <;> rfl
  · have ha := hall a (by simp)
    have hb := hall b (by simp)
    subst a; subst b
    rcases hop with rfl | rfl <;> rfl
  · simp at hlen

lemma four_chain_skips (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (hfour : FourOneChain n C u) :
    (elim n C.gates (initAt n u true, [])).2.length + 4 ≤ C.gates.length := by
  classical
  obtain ⟨a, b, c, d, hnd, ha, hb, hc, hd, hac, hbc, hcd,
    hoa, hob, hua, hub, hca, hcb, hdc⟩ := hfour
  have hab : a ≠ b := by simpa using (List.nodup_cons.mp hnd).1 b (by simp)
  have hsa := input_skips n C hC u true a ha hua
  have hsb := input_skips n C hC u true b hb hub
  have hca' : n + a ∈ C.gates[c].inputs := by rwa [gateAt_get C c hc] at hca
  have hcb' : n + b ∈ C.gates[c].inputs := by rwa [gateAt_get C c hc] at hcb
  have hcca := or_input_one n C hC u a c hac (le_of_lt hc) hoa hua
  have hccb := or_input_one n C hC u b c hbc (le_of_lt hc) hob hub
  have hsc : skips n C.gates (initAt n u true, []) c :=
    const_skips n C.gates _ c hc (mono_nok C hC c hc) (n + a) hca' true hcca
  have hcout : (simplify C.gates[c].op
      (n + (prefix n C.gates (initAt n u true, []) c).2.length)
      (C.gates[c].inputs.map fun i =>
        (prefix n C.gates (initAt n u true, []) c).1.getD i (Sum.inl false))).2 =
      Sum.inl true := by
    have he := simplify_all_one C.gates[c].op (hC _ (List.getElem_mem hc)).1
      (n + (prefix n C.gates (initAt n u true, []) c).2.length)
      (C.gates[c].inputs.map fun i =>
        (prefix n C.gates (initAt n u true, []) c).1.getD i (Sum.inl false))
      (by simpa using (hC _ (List.getElem_mem hc)).2)
      (by intro hn; have := List.mem_map.mpr ⟨n + a, hca', rfl⟩; rw [hn] at this; simpa using this)
      (by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
        rcases two_members_cover C.gates[c].inputs (hC _ (List.getElem_mem hc)).2
          (n + a) (n + b) (by omega) hca' hcb' i hi with rfl | rfl
        · exact hcca
        · exact hccb)
    rw [he]
  have hcdconst : (prefix n C.gates (initAt n u true, []) d).1.getD (n + c) (Sum.inl false)
      = Sum.inl true := by
    simpa only [initAt_length] using
      gate_const_before n C.gates (initAt n u true, []) c d hcd (le_of_lt hd) true hcout
  have hsd : skips n C.gates (initAt n u true, []) d := by
    rw [gateAt_get C d hd] at hdc
    exact const_skips n C.gates _ d hd (mono_nok C hC d hd) (n + c) hdc true hcdconst
  have hh := marked_skips_bound n C.gates (initAt n u true, []) [a, b, c, d].toFinset (by
    intro j hj
    simp only [List.mem_toFinset, List.mem_cons, List.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact ⟨ha, hsa⟩
    · exact ⟨hb, hsb⟩
    · exact ⟨hc, hsc⟩
    · exact ⟨hd, hsd⟩)
  simpa [List.toFinset_card_of_nodup hnd] using hh

lemma inv_initAt (n : ℕ) (u : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x u b)) (initAt n u b, []) := by
  refine ⟨by simp [initAt], ?_⟩
  intro i
  by_cases hi : i < n
  · have hs : (initAt n u b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin n) = u then Sum.inl b else Sum.inr i := by
      simp [initAt, List.getD_eq_getElem?_getD, hi]
    rw [hs]
    by_cases hu : (⟨i, hi⟩ : Fin n) = u
    · simp [hu, Stat.Valid, Stat.val, wiresFrom, List.getD_eq_getElem?_getD, hi,
        Function.update_apply]
    · simp [hu, Stat.Valid, Stat.val, wiresFrom, List.getD_eq_getElem?_getD, hi,
        Function.update_apply]
  · have hs : (initAt n u b).getD i (Sum.inl false) = Sum.inl false := by
      apply List.getD_eq_default
      simp [initAt]
      omega
    rw [hs]
    have ho : (List.ofFn (Function.update x u b)).getD i false = false := by
      apply List.getD_eq_default
      simp
      omega
    rw [ho]
    simp [Stat.Valid, Stat.val]

lemma compile_restriction (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n) (b : Bool)
    (hzero : C.eval (List.ofFn (Function.update (fun _ : Fin n => false) u b)) = false) :
    HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn (Function.update x u b)))
      (elim n C.gates (initAt n u b, [])).2.length := by
  let acc := elim n C.gates (initAt n u b, [])
  have hOk : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hC g hg
    refine ⟨?_, hlen⟩
    rcases hop with ha | ho
    · exact Or.inl ha
    · exact Or.inr (Or.inl ho)
  have houtOk : ∀ g ∈ acc.2, Ok g := elim_ok n C.gates _ (by simp)
  have hi (x : Fin n → Bool) :
      Inv n (List.ofFn x) (C.wires (List.ofFn (Function.update x u b))) acc :=
    inv_elim n (List.ofFn x) (by simp) C.gates _ _ hOk (inv_initAt n u b x)
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    cases c with
    | false =>
      refine ⟨⟨acc.2, n + acc.2.length⟩, houtOk, le_rfl, ?_⟩
      intro x
      have hv := (hi x).2 C.output
      rw [ho] at hv
      have he : (⟨acc.2, n + acc.2.length⟩ : Circuit).eval (List.ofFn x) = false := by
        change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = false
        apply List.getD_eq_default
        simp [length_wiresFrom]
      rw [he]
      exact hv.2
    | true =>
      have hv := (hi (fun _ => false)).2 C.output
      rw [ho] at hv
      have hh : true = C.eval (List.ofFn (Function.update (fun _ : Fin n => false) u b)) := hv.2
      rw [hzero] at hh
      contradiction
  | inr o =>
    refine ⟨⟨acc.2, o⟩, houtOk, le_rfl, ?_⟩
    intro x
    have hv := (hi x).2 C.output
    rw [ho] at hv
    exact hv.2

lemma restrict_three (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (hzero : C.eval (List.ofFn (Function.update (fun _ : Fin n => false) u false)) = false)
    (hc : ThreeZero n C u) :
    ∃ s, s + 3 ≤ C.size ∧
      HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn (Function.update x u false))) s := by
  exact ⟨_, three_skips n C hC u hc, compile_restriction n C hC u false hzero⟩

lemma restrict_four (n : ℕ) (C : Circuit) (hC : Monotone2 C) (u : Fin n)
    (hzero : C.eval (List.ofFn (Function.update (fun _ : Fin n => false) u true)) = false)
    (hc : FourOneFork n C u ∨ FourOneChain n C u) :
    ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x : Fin n → Bool => C.eval (List.ofFn (Function.update x u true))) s := by
  refine ⟨_, ?_, compile_restriction n C hC u true hzero⟩
  rcases hc with h | h
  · exact four_fork_skips n C hC u h
  · exact four_chain_skips n C hC u h

end PEqualNP.Outside.L_meta_1031.CycleElim
