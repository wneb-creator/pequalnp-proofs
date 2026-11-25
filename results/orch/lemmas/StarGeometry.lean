import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2448

lemma common_center_of_pairwise_meeting {V : Type*} (G : SimpleGraph V)
    (r : V → V → Prop)
    (hadj : ∀ {u v}, r u v → G.Adj u v)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmeet : ∀ {a b c d}, r a b → r c d →
      a = c ∨ a = d ∨ b = c ∨ b = d) :
    (∀ u v, ¬ r u v) ∨ ∃ c, ∀ u v, r u v → u = c ∨ v = c := by
  classical
  by_cases used : ∃ a b, r a b
  · obtain ⟨a, b, hab⟩ := used
    right
    by_cases ha : ∀ u v, r u v → u = a ∨ v = a
    · exact ⟨a, ha⟩
    · simp only [not_forall, Classical.not_imp] at ha
      obtain ⟨p, q, hpq, hna⟩ := ha
      have hpa : p ≠ a := fun h => hna (Or.inl h)
      have hqa : q ≠ a := fun h => hna (Or.inr h)
      have hbpq : p = b ∨ q = b := by
        rcases hmeet hpq hab with h | h | h | h
        · exact (hpa h).elim
        · exact Or.inl h
        · exact (hqa h).elim
        · exact Or.inr h
      have hext : ∃ w, w ≠ a ∧ G.Adj b w ∧
          ∀ u v, r u v → u = b ∨ v = b ∨ u = w ∨ v = w := by
        rcases hbpq with rfl | rfl
        · refine ⟨q, hqa, hadj hpq, ?_⟩
          intro u v huv
          rcases hmeet huv hpq with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))
        · refine ⟨p, hpa, (hadj hpq).symm, ?_⟩
          intro u v huv
          rcases hmeet huv hpq with h | h | h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inr (Or.inl h)
      obtain ⟨w, hwa, hbw, hmeetw⟩ := hext
      refine ⟨b, ?_⟩
      intro u v huv
      by_contra hnb
      have hub : u ≠ b := fun h => hnb (Or.inl h)
      have hvb : v ≠ b := fun h => hnb (Or.inr h)
      have huva : u = a ∨ v = a := by
        rcases hmeet huv hab with h | h | h | h
        · exact Or.inl h
        · exact (hub h).elim
        · exact Or.inr h
        · exact (hvb h).elim
      have huvw : u = w ∨ v = w := by
        rcases hmeetw u v huv with h | h | h | h
        · exact (hub h).elim
        · exact (hvb h).elim
        · exact Or.inl h
        · exact Or.inr h
      have hwa_adj : G.Adj w a := by
        rcases huva with rfl | rfl
        · have hvw := huvw.resolve_left hwa.symm
          simpa only [hvw] using (hadj huv).symm
        · have huw := huvw.resolve_right hwa.symm
          simpa only [huw] using hadj huv
      exact htriangle a b w (hadj hab) hbw hwa_adj
  · left
    exact fun u v huv => used ⟨u, v, huv⟩

set_option maxHeartbeats 1000000 in
lemma owned_disjoint_edges_have_false_positive (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (hm : Monotone2 C)
  (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
  (a b c d : Fin n)
  (ab : Owns n C j a b) (cd : Owns n C j c d)
  (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
  ∃ u ∈ ({a,b,c,d} : Finset (Fin n)), ∃ v ∈ ({a,b,c,d} : Finset (Fin n)), ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  classical
  let stepWire (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wires_eq_foldl (C : Circuit) (x : List Bool) :
      C.wires x = C.gates.foldl stepWire x := rfl

  have foldl_stepWire_length (gs : List Gate) (w : List Bool) :
      (gs.foldl stepWire w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [stepWire]
      omega

  have foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl stepWire w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
      rw [ih (stepWire w g) hlt]
      simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

  have getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
      w.getD i false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

  have split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      ∃ (pre post : List Gate) (gj : Gate),
        gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
    refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
    rw [List.cons_getElem_drop_succ, List.take_append_drop]

  let W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
    (C.wires (List.ofFn x)).getD u false

  have gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
    change C.gates.getD k _ = _
    simp [List.getD_eq_getElem?_getD, hk]

  have W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
      W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < n + k then W n C x i else false) := by
    obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
    have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
    rw [hga]
    let w0 := pre.foldl stepWire (List.ofFn x)
    have hw0_len : w0.length = n + k := by
      simp [w0, foldl_stepWire_length, hpre_len]
    have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
      simp only [W]
      rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
      rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
    rw [hCj]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    by_cases hi : i < n + k
    · simp only [hi, ↓reduceIte]
      simp only [W]
      rw [wires_eq_foldl, hgs, List.foldl_append]
      exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
    · simp only [hi, ↓reduceIte]
      exact getD_ge_length w0 i (by omega)

  have W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
      W n C x u = x ⟨u, hu⟩ := by
    simp only [W]
    rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
    simp [List.getD_eq_getElem?_getD, hu]

  have coneEq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl
  have coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneEq]
      omega

  have coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      (coneStep n cs g).getD cs.length [] =
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) []) := by
    simp [coneEq, List.getD_eq_getElem?_getD]

  have coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
      (coneStep n cs g).getD m [] = cs.getD m [] := by
    simp [coneEq, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

  have coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
      (hk : k < cs.length) :
      (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (coneStep n cs g) (by simp [coneEq]; omega)]
      exact coneStep_getD_lt n cs g k hk

  have inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
      InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        (i = w - n ∨ InCone n C i (w - n)) := by
    obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
    have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
    rw [hga]
    have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
      delta cones
      rw [hgs, List.foldl_append, List.foldl_cons]
    have hl0 : (pre.foldl (coneStep n) []).length = k := by
      rw [coneFold_length]; simp [hpre_len]
    have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
      simp [coneEq, hl0]
    have h1 : (cones n C).getD k [] =
        (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
          (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
      rw [hc, coneFold_getD_lt n post _ k (by omega)]
      have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
      rw [hl0] at h
      exact h
    have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
      intro m hm
      rw [hc, coneFold_getD_lt n post _ m (by omega)]
      exact coneStep_getD_lt n _ gk m (by omega)
    unfold InCone
    rw [h1]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
      refine ⟨w, hw, hn, hlt, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [h2 (w - n) (by omega)]
        exact h
    · rintro ⟨w, hw, hn, hlt, h⟩
      refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [← h2 (w - n) (by omega)]
        exact h


  have ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
      (if c then b else false) = true ↔ c ∧ b = true := by
    by_cases h : c <;> simp [h]

  have W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.and) :
      W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
    rw [W_gate n C x k hk, hop]
    have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    simp only [andEval, List.all_eq_true, List.mem_map, id_eq]
    constructor
    · intro h w hw
      exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
    · rintro h b ⟨w, hw, rfl⟩
      exact (ite_true_iff _ _).mpr (h w hw)

  have W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) :
      W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
    rw [W_gate n C x k hk, hop]
    have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    simp only [orEval, List.any_eq_true, List.mem_map, id_eq]
    constructor
    · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
      exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

  have inCone_lt (n : ℕ) (C : Circuit) :
      ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i hi
      obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
      rcases h with h | h
      · omega
      · have := ih (w - n) (by omega) (by omega) i h
        omega

  have gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
        (gateAt C k).inputs.length ≤ 2 := by
    have hg := hM (C.gates[k]) (List.getElem_mem hk)
    rw [← gateAt_eq C k hk] at hg
    have h1 := hg.1
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, hg.2⟩

  let Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
    ∀ P : ℕ → Prop, P t.val →
      (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
        ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

  have reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

  have reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
      (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
      (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
    fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

  have reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
      (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
    h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
      (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

  have descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
      ∀ k, k < C.gates.length → W n C x (n + k) = true →
        (gateAt C k).op = GateOp.and ∨
        (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
        (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hx
      rcases (gate_mono2 C hM k hk).1 with hop | hop
      · exact Or.inl hop
      · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
        by_cases hwn : w < n
        · right; right
          refine ⟨⟨w, hwn⟩, ?_, ?_⟩
          · rw [← W_input n C x w hwn]; exact hwx
          · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
        · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
          have he : n + k' - n = k' := by omega
          rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
          · right; left
            exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
              h, hwx⟩
          · right; left
            exact ⟨i, (inCone_iff n C i k hk).mpr
              ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
          · right; right
            exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

  have owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
      (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
      ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
    obtain ⟨_, _, hval, hno⟩ := ho
    intro w hw
    have hval' : W n C (pairInput p q) (n + j) = true := hval
    obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
    refine ⟨hlt, ?_⟩
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hwx
      have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
      rcases h' with h | h
      · left
        rw [← h]; exact reach_refl n C ⟨w, hwn⟩
      · right
        rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
      have he : n + k' - n = k' := by omega
      have hk'j : k' < j := by omega
      have hc : InCone n C k' j :=
        (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
      rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
      · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
        rw [hwx] at hf
        exact absurd hf (by simp)
      · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
          ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
        have hij := inCone_lt n C j hj i hc2
        have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
        rw [hix] at hf
        exact absurd hf (by simp)
      · have h' : t = p ∨ t = q := of_decide_eq_true ht
        rcases h' with h | h
        · left; rw [← h]; exact hdom
        · right; rw [← h]; exact hdom
  let S : Finset (Fin n) := {a,b,c,d}
  change ∃ u ∈ S, ∃ v ∈ S, ¬G.Adj u v ∧ gateVal n C j (pairInput u v) = true
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hcS : c ∈ S := by simp [S]
  have hdS : d ∈ S := by simp [S]
  by_contra! clean
  have F3 (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S)
      (hr : ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C s w ∨ Reach n C t w)) :
      G.Adj s t := by
    by_contra hst
    have hs : pairInput s t s = true := decide_eq_true (Or.inl rfl : s = s ∨ s = t)
    have ht : pairInput s t t = true := decide_eq_true (Or.inr rfl : t = s ∨ t = t)
    have hval : W n C (pairInput s t) (n + j) = true :=
      (W_and_iff n C _ j ab.1 ab.2.1).mpr (fun w hw => ⟨(hr w hw).1,
        (hr w hw).2.elim (fun h => reach_val n C s w _ hs h) (fun h => reach_val n C t w _ ht h)⟩)
    have hval' : gateVal n C j (pairInput s t) = true := hval
    have hfalse := clean s hsS t htS hst
    simp [hval'] at hfalse
  have reach {s t : Fin n} (h : Owns n C j s t) := owns_reach n C hm j ab.1 ab.2.1 s t h
  have hlen := (gate_mono2 C hm j ab.1).2
  rcases hin : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨t, ts⟩⟩⟩
  · exact (F3 a a haS haS (by simp [hin])).ne rfl
  · have h := reach ab p (by simp [hin])
    rcases h.2 with ha | hb
    · exact (F3 a a haS haS (by simpa [hin] using And.intro h.1 ha)).ne rfl
    · exact (F3 b b hbS hbS (by simpa [hin] using And.intro h.1 hb)).ne rfl
  · have hp := (reach ab p (by simp [hin])).1
    have hq := (reach ab q (by simp [hin])).1
    have cross (s t : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (hs : Reach n C s p) (ht : Reach n C t q) : G.Adj s t := by
      apply F3 s t hsS htS
      intro w hw
      simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨hp, Or.inl hs⟩
      · exact ⟨hq, Or.inr ht⟩
    have sides {s t : Fin n} (hsS : s ∈ S) (htS : t ∈ S) (h : Owns n C j s t) :
        (Reach n C s p ∧ Reach n C t q) ∨ (Reach n C t p ∧ Reach n C s q) := by
      rcases (reach h p (by simp [hin])).2 with hs | ht <;>
        rcases (reach h q (by simp [hin])).2 with hu | hv
      · exact ((cross s s hsS hsS hs hu).ne rfl).elim
      · exact Or.inl ⟨hs, hv⟩
      · exact Or.inr ⟨ht, hu⟩
      · exact ((cross t t htS htS ht hv).ne rfl).elim
    have rectangle (s t u v : Fin n) (hsS : s ∈ S) (htS : t ∈ S) (huS : u ∈ S) (hvS : v ∈ S)
        (hs : Reach n C s p) (ht : Reach n C t q)
        (hu : Reach n C u p) (hv : Reach n C v q) : s = u ∨ t = v :=
      hfour s t u v (cross s t hsS htS hs ht) (cross u t huS htS hu ht).symm (cross u v huS hvS hu hv) (cross s v hsS hvS hs hv).symm
    rcases sides haS hbS ab with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rcases sides hcS hdS cd with ⟨hc, hd⟩ | ⟨hd, hc⟩
    · exact (rectangle a b c d haS hbS hcS hdS ha hb hc hd).elim hac hbd
    · exact (rectangle a b d c haS hbS hdS hcS ha hb hd hc).elim had hbc
    · exact (rectangle b a c d hbS haS hcS hdS hb ha hc hd).elim hbc had
    · exact (rectangle b a d c hbS haS hdS hcS hb ha hd hc).elim hbd hac
  · simp [hin] at hlen

lemma hasStarProfile_of_pairwise_meeting (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmeet : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b c d, G.Adj a b → G.Adj c d → Owns n C j a b → Owns n C j c d →
        a = c ∨ a = d ∨ b = c ∨ b = d) : HasStarProfile n G C := by
  intro j hj hop
  rcases common_center_of_pairwise_meeting G
      (fun u v => G.Adj u v ∧ Owns n C j u v)
      (fun h => h.1) htriangle
      (fun h₁ h₂ => hmeet j hj hop _ _ _ _ h₁.1 h₂.1 h₁.2 h₂.2) with h | ⟨c, hc⟩
  · left
    exact fun u v huv hov => h u v ⟨huv, hov⟩
  · right
    exact ⟨c, fun u v huv hov => hc u v ⟨huv, hov⟩⟩

lemma hasStarProfile_of_pair_sound (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (hm : Monotone2 C)
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (hclean : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ u v, gateVal n C j (pairInput u v) = true → G.Adj u v) :
    HasStarProfile n G C := by
  apply hasStarProfile_of_pairwise_meeting n G C htriangle
  intro j hj hop a b c d _ _ hab hcd
  by_contra hmeet
  have hac : a ≠ c := fun h => hmeet (Or.inl h)
  have had : a ≠ d := fun h => hmeet (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hmeet (Or.inr (Or.inr (Or.inl h)))
  have hbd : b ≠ d := fun h => hmeet (Or.inr (Or.inr (Or.inr h)))
  obtain ⟨u, _, v, _, hnon, hfire⟩ :=
    owned_disjoint_edges_have_false_positive n G C j hm hfour a b c d hab hcd hac had hbc hbd
  exact hnon (hclean j hj hop u v hfire)

end PEqualNP.Outside.L_meta_2448
