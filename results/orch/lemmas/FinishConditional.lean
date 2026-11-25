import PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive SolCount (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {S : Set ℕ} : T ∈ S → SolCount R m T 0 0 S
  | pad {q n e : ℕ} {S : Set ℕ} : e ≤ 1 → SolCount R m T q n S →
      SolCount R m T (q + 1) (n + e) S
  | un {q n : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S →
      SolCount R m T q n (insert (a ^^^ m) S) → SolCount R m T (q + 1) (n + 1) S
  | bi {q n : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      SolCount R m T q n (insert (op d a b) S) → SolCount R m T (q + 1) n S

lemma SolCount.live {m T q n : ℕ} {S : Set ℕ} (h : SolCount R m T q n S) :
    ∃ k t : ℕ, t ≤ n ∧ k + (n - t) ≤ q ∧
      ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done S h => exact ⟨0, 0, by omega, by omega, {T}, by simpa using h, .stop⟩
  | @pad q n e S he h ih =>
    obtain ⟨k, t, ht, hk, S0, hs, hl⟩ := ih
    exact ⟨k, t, by omega, by omega, S0, hs, hl⟩
  | @un q n S a ha h ih =>
    obtain ⟨k, t, ht, hk, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, t + 1, by omega, by omega,
        insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, t, by omega, by omega, S1,
        fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q n S d a b ha hb hal h ih =>
    obtain ⟨k, t, ht, hk, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab
        rw [op_self] at hs
        exact ⟨k, t, ht, by omega, S1,
          fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, t, ht, by omega,
        insert a (insert b (S1.erase (op d a b))), ?_,
        .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, t, ht, by omega, S1,
        fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

open PEqualNP.CircuitLowerBounds

noncomputable def notCount (gs : List Gate) : ℕ := by
  classical
  exact gs.countP (fun g => decide (g.op = GateOp.not))

lemma notCount_nil : notCount [] = 0 := by simp [notCount]

lemma notCount_cons (g : Gate) (gs : List Gate) :
    notCount (g :: gs) = notCount gs + notCount [g] := by
  classical
  simp [notCount, List.countP_cons]

lemma notCount_single_le (g : Gate) : notCount [g] ≤ 1 := by
  classical
  simp only [notCount, List.countP_cons, List.countP_nil, zero_add]
  split_ifs <;> omega

lemma ex_solCount (m : ℕ) {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → SolCount Z0 m T gs.length (notCount gs) S := by
  classical
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → SolCount Z0 m T (g :: gs).length (notCount (g :: gs)) S := by
      intro hv
      rw [List.length_cons, notCount_cons]
      apply SolCount.pad (notCount_single_le g)
      exact ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact hv) h0 hm hgs hT
    have go : SolCount Z0 m T gs.length (notCount gs) (insert (gv m w g) S) :=
      ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [notCount_cons, notCount, op, gv] using
          (SolCount.bi (d := false) (rd i) (rd j) (al0 _ _ _) go)
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [notCount_cons, notCount, op, gv] using
          (SolCount.bi (d := true) (rd i) (rd j) (al0 _ _ _) go)
    · match l with
      | [] => exact stay hm
      | i :: _ =>
        simpa [notCount_cons, notCount, gv] using (SolCount.un (rd i) go)

lemma bridgeCount (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = f y) :
    SolCount Z0 (mz 0) (tz 0) D.size (notCount D.gates) (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 7 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true →
      init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq
    intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_solCount (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩

lemma circuit_live_count (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = f y) :
    ∃ k t : ℕ, t ≤ notCount D.gates ∧ k + (notCount D.gates - t) ≤ D.size ∧
      ∃ S : Finset ℕ, (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧
        Live Z0 (mz 0) (tz 0) k t S :=
  (bridgeCount D hD hf).live

lemma unique_not_count (gs : List Gate)
    (h : ∀ i j : Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    notCount gs ≤ 1 := by
  classical
  unfold notCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases hg : g.op = GateOp.not
    · have hz : gs.countP (fun g => decide (g.op = GateOp.not)) = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro haNot
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have hiNot : (gs.get i).op = GateOp.not := by rw [hi]; exact haNot
        have hh := h ⟨0, by simp⟩ i.succ (by simpa using hg)
          (by simpa using hiNot)
        have hv := congrArg Fin.val hh
        simp at hv
      simp [List.countP_cons, hg, hz]
    · have ht : ∀ i j : Fin gs.length,
          (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j := by
        intro i j hi hj
        exact Fin.succ_inj.mp (h i.succ j.succ (by simpa using hi) (by simpa using hj))
      simpa [List.countP_cons, hg] using ih ht


lemma live_certificate_false {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L)
    (hp : pOk Z Q = true) (hL : L ≤ 15) (hk : k < L)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z))
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : ∃ M : List (ℕ × ℕ), mFull M = true ∧
      ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneNotLiveImpossible
    (hcheck : chk [] (pr ac4 0) 0 13 1 FF 1 = false)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 13 1 S) : False := by
  apply live_certificate_false (E := []) (Q := pr ac4 0) (Z := 0) (L := 14)
    (Or.inl rfl) (by decide +kernel) (by omega) (by omega)
    (fun e he => ai4 e (List.mem_of_mem_filter he)) hS hl
    (fun q hq => iroot q hq)
  refine ⟨[(FF, 1)], ffull, ?_⟩
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact hcheck

lemma finish_if (hOneNot : chk [] (pr ac4 0) 0 13 1 FF 1 = false) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  classical
  intro gates o legal oneNot computes
  by_cases hbig : 14 ≤ gates.length
  · exact ⟨witness, 20, witness_basis, by simpa [witness_length] using hbig,
      fun x => (witness_correct x).trans (graph_correct x)⟩
  by_cases hzero : notCount gates = 0
  · have hn : ∀ g ∈ gates, g.op ≠ GateOp.not := by
      simpa only [notCount, List.countP_eq_zero, decide_eq_true_eq] using hzero
    refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn g hg h)
  have hn : notCount gates = 1 := by
    have := unique_not_count gates oneNot
    omega
  have hok : FanInTwo (⟨gates, o⟩ : Circuit) := by
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h <;> simp [h]
  have hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x :=
    fun x => (computes x).trans (graph_correct x).symm
  obtain ⟨k, t, ht, hb, S, hS, hl⟩ := circuit_live_count ⟨gates, o⟩ hok hf
  have hk : 13 ≤ k := by
    by_contra h
    exact iroot k (by omega) (hl.sol.mono le_rfl hS)
  change t ≤ notCount gates at ht
  change k + (notCount gates - t) ≤ gates.length at hb
  rw [hn] at ht hb
  have hkEq : k = 13 := by omega
  have htEq : t = 1 := by omega
  subst k
  subst t
  exact False.elim (oneNotLiveImpossible hOneNot S hS hl)

end PEqualNP.Outside.L_meta_10760
