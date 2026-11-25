open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma owns_bipartite_on_singleton_silent (n : ℕ) (C : Circuit) (j : ℕ)
    (S : Set (Fin n))
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hs : ∀ u ∈ S, gateVal n C j (pairInput u u) = false) :
    ∃ color : Fin n → Bool, ∀ u ∈ S, ∀ v ∈ S,
      Owns n C j u v → color u ≠ color v := by
  by_cases hex : ∃ u ∈ S, ∃ v ∈ S, Owns n C j u v
  · obtain ⟨u0, hu0, v0, hv0, ho⟩ := hex
    have hj := ho.1
    have hop := ho.2.1
    rw [gateAt_eq C j hj] at hop
    let val (i : ℕ) (u : Fin n) :=
      (wf (C.gates.take j) (List.ofFn (pairInput u u))).getD i false
    have polar (u v : Fin n) (ho : Owns n C j u v) (i : ℕ)
        (hi : i ∈ C.gates[j].inputs) : val i u = true ∨ val i v = true := by
      have hown : ∀ k, InCone n C k j → (gateAt C k).op = GateOp.and →
          gateVal n C k (pairInput u v) = false :=
        fun k hc ha => ho.2.2.2 k (cone_idx n C.gates j k hc) hc ha
      have hv := ho.2.2.1
      rw [valf n C _ j hj, hop] at hv
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv
      obtain ⟨w, hw, hr⟩ := wire_reach n C hm _ j hj
        (fun k hk a b c => or_reach n C hm _ k (lt_trans hk hj) a b c)
        hown i hi (hv i hi)
      have hwu : w = u ∨ w = v := of_decide_eq_true hw
      rcases hwu with rfl | rfl
      · exact Or.inl (hr _ (by simp [pairInput]))
      · exact Or.inr (hr _ (by simp [pairInput]))
    have silent (u : Fin n) (hu : u ∈ S) (hr : ∀ i ∈ C.gates[j].inputs, val i u = true) : False := by
      have hv : gateVal n C j (pairInput u u) = true := by
        rw [valf n C _ j hj, hop]
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        exact hr
      rw [hs u hu] at hv
      contradiction
    have hlen := (hm _ (List.getElem_mem hj)).2
    match hin : C.gates[j].inputs, hlen with
    | [], _ => exact (silent u0 hu0 (by simp [hin])).elim
    | [p], _ =>
      rcases polar u0 v0 ho p (by simp [hin]) with hu | hv
      · exact (silent u0 hu0 (by simpa [hin] using hu)).elim
      · exact (silent v0 hv0 (by simpa [hin] using hv)).elim
    | [p, q], _ =>
      have separate (u : Fin n) (hu : u ∈ S) (hp : val p u = true) (hq : val q u = true) : False := by
        apply silent u hu
        intro i hi
        rcases (by simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hi :
            i = p ∨ i = q) with rfl | rfl
        · exact hp
        · exact hq
      refine ⟨val p, ?_⟩
      intro u hu v hv huv he
      have hup := polar u v huv p (by simp [hin])
      have huq := polar u v huv q (by simp [hin])
      rcases hup with hup | hvp <;> rcases huq with huq | hvq
      · exact separate u hu hup huq
      · exact separate v hv (he ▸ hup) hvq
      · exact separate u hu (he.symm ▸ hvp) huq
      · exact separate v hv hvp hvq
    | _ :: _ :: _ :: _, h => simp at h
  · refine ⟨fun _ => false, ?_⟩
    intro u hu v hv ho
    exact (hex ⟨u, hu, v, hv, ho⟩).elim

lemma owns_bipartite_of_singleton_silent (n : ℕ) (C : Circuit) (j : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hs : ∀ u : Fin n, gateVal n C j (pairInput u u) = false) :
    ∃ color : Fin n → Bool, ∀ u v : Fin n,
      Owns n C j u v → color u ≠ color v := by
  obtain ⟨color, hc⟩ := owns_bipartite_on_singleton_silent n C j Set.univ hm (fun u _ => hs u)
  exact ⟨color, fun u v ho => hc u (Set.mem_univ u) v (Set.mem_univ v) ho⟩

lemma odd_owned_closed_walk_has_singleton (n : ℕ) (C : Circuit) (j k : ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (p : ℕ → Fin n)
    (hclosed : p (2 * k + 1) = p 0)
    (hown : ∀ i < 2 * k + 1, Owns n C j (p i) (p (i + 1))) :
    ∃ i ≤ 2 * k + 1, gateVal n C j (pairInput (p i) (p i)) = true := by
  by_contra! hnone
  let S : Set (Fin n) := {u | ∃ i ≤ 2 * k + 1, p i = u}
  have hs : ∀ u ∈ S, gateVal n C j (pairInput u u) = false := by
    rintro u ⟨i, hi, rfl⟩
    exact Bool.eq_false_iff.mpr (hnone i hi)
  obtain ⟨color, hc⟩ := owns_bipartite_on_singleton_silent n C j S hm hs
  have step (i : ℕ) (hi : i < 2 * k + 1) : color (p i) ≠ color (p (i + 1)) :=
    hc (p i) ⟨i, by omega, rfl⟩ (p (i + 1)) ⟨i + 1, by omega, rfl⟩ (hown i hi)
  have two (a b c : Bool) (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
    cases a <;> cases b <;> cases c <;> simp_all
  have even (m : ℕ) (hmk : m ≤ k) : color (p (2 * m)) = color (p 0) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      have h1 := step (2 * m) (by omega)
      have h2 := step (2 * m + 1) (by omega)
      have he := two _ _ _ h1 h2
      calc
        color (p (2 * (m + 1))) = color (p (2 * m)) := by
          convert he.symm using 1
        _ = color (p 0) := ih (by omega)
  have hlast := step (2 * k) (by omega)
  rw [hclosed, even k (le_refl k)] at hlast
  exact hlast rfl
