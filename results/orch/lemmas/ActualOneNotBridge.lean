import ComputationalRoot13

namespace PEqualNP.Outside.L_meta_10760_aux

variable {R : ℕ → ℕ}

def SolD (R : ℕ → ℕ) (m T q t : ℕ) (S : Set ℕ) : Prop :=
  ∃ k ≤ q, ∃ u ≤ t, ∃ S0 : Finset ℕ,
    (S0 : Set ℕ) ⊆ S ∧ Live R m T k u S0 ∧ k + t ≤ q + u

lemma SolD.mono {m T q t : ℕ} {S : Set ℕ} (h : SolD R m T q t S)
    {q' t' : ℕ} {S' : Set ℕ} (hq : q ≤ q') (ht : t ≤ t')
    (hd : q + t' ≤ q' + t) (hS : S ⊆ S') : SolD R m T q' t' S' := by
  obtain ⟨k, hk, u, hu, S0, hs, hl, hdef⟩ := h
  exact ⟨k, hk.trans hq, u, hu.trans ht, S0, hs.trans hS, hl, by omega⟩

lemma SolD.done {m T q t : ℕ} {S : Set ℕ} (h : T ∈ S) (ht : t ≤ q) :
    SolD R m T q t S :=
  ⟨0, by omega, 0, by omega, {T}, by simpa using h, .stop, by omega⟩

lemma SolD.un {m T q t a : ℕ} {S : Set ℕ}
    (ha : a ∈ S) (h : SolD R m T q t (insert (a ^^^ m) S)) :
    SolD R m T (q + 1) (t + 1) S := by
  obtain ⟨k, hk, u, hu, S1, hs, hl, hdef⟩ := h
  by_cases hg : a ^^^ m ∈ S1
  · refine ⟨k + 1, by omega, u + 1, by omega,
      insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg]), by omega⟩
    intro x hx
    simp at hx
    rcases hx with rfl | ⟨h1, h2⟩
    · exact ha
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, u, by omega, S1,
      fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl, by omega⟩

lemma SolD.bi {m T q t a b : ℕ} {d : Bool} {S : Set ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hal : Al R d a b)
    (h : SolD R m T q t (insert (op d a b) S)) :
    SolD R m T (q + 1) t S := by
  obtain ⟨k, hk, u, hu, S1, hs, hl, hdef⟩ := h
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab
      rw [op_self] at hs
      exact ⟨k, by omega, u, hu, S1,
        fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl, by omega⟩
    refine ⟨k + 1, by omega, u, hu,
      insert a (insert b (S1.erase (op d a b))), ?_,
      .bi hab hal (by rwa [Finset.insert_erase hg]), by omega⟩
    intro x hx
    simp at hx
    rcases hx with rfl | rfl | ⟨h1, h2⟩
    · exact ha
    · exact hb
    · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, u, hu, S1,
      fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl, by omega⟩

lemma SolD.toSol {m T q t : ℕ} {S : Set ℕ} (h : SolD R m T q t S) :
    Sol Z0 m T q S := by
  obtain ⟨k, hk, u, _, S0, hs, hl, _⟩ := h
  exact hl.sol.mono hk hs

lemma SolD.live_minimal {m T q t : ℕ} {S : Set ℕ} (h : SolD R m T q t S)
    (hmin : ∀ k < q, ¬ Sol Z0 m T k S) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T q t S0 := by
  obtain ⟨k, hk, u, hu, S0, hs, hl, hdef⟩ := h
  have hq : k = q := by
    by_contra hne
    exact hmin k (by omega) (hl.sol.mono le_rfl hs)
  have ht : u = t := by omega
  subst k
  subst u
  exact ⟨S0, hs, hl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section counted
variable (m : ℕ)
def notWeight : GateOp → ℕ
  | .not => 1
  | _ => 0

lemma notWeight_zero {o : GateOp} (h : o ≠ GateOp.not) : notWeight o = 0 := by
  cases o <;> simp_all [notWeight]

lemma notWeight_le_one (o : GateOp) : notWeight o ≤ 1 := by
  cases o <;> simp [notWeight]

def countNot : List Gate → ℕ
  | [] => 0
  | g :: gs => countNot gs + notWeight g.op

lemma countNot_tail_le (g : Gate) (gs : List Gate) : countNot gs ≤ countNot (g :: gs) := by
  simp [countNot]

lemma countNot_zero (gs : List Gate) (h : ∀ i : Fin gs.length,
    (gs.get i).op ≠ GateOp.not) : countNot gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op ≠ GateOp.not := h 0
    have ht : ∀ i : Fin gs.length, (gs.get i).op ≠ GateOp.not := fun i => h i.succ
    simp [countNot, notWeight_zero hg, ih ht]

lemma countNot_le_one (gs : List Gate)
    (h : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : countNot gs ≤ 1 := by
  induction gs with
  | nil => simp [countNot]
  | cons g gs ih =>
    have ht : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
        (gs.get j).op = GateOp.not → i = j := by
      intro i j hi hj
      exact Fin.succ_inj.mp (h i.succ j.succ hi hj)
    by_cases hg : g.op = GateOp.not
    · have hn : ∀ j : Fin gs.length, (gs.get j).op ≠ GateOp.not := by
        intro j hj
        have e := congrArg Fin.val (h 0 j.succ hg hj)
        simp at e
      simp [countNot, hg, notWeight, countNot_zero gs hn]
    · simpa [countNot, notWeight_zero hg] using ih ht

lemma ex_solD {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → SolD Z0 m T gs.length (countNot gs) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i) (by simp [countNot])
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → SolD Z0 m T (g :: gs).length (countNot (g :: gs)) S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) (countNot_tail_le g gs) (by
          simp only [List.length_cons, countNot]
          have := notWeight_le_one g.op
          omega) subset_rfl
    have go : SolD Z0 m T gs.length (countNot gs) (insert (gv m w g) S) :=
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
      | i :: j :: _ => simpa [countNot, notWeight] using SolD.bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => simpa [countNot, notWeight] using SolD.bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => simpa [countNot, notWeight] using SolD.un (rd i) go

lemma countNot_pos (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    1 ≤ countNot gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨w, hw, ho⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [countNot, ho, notWeight]
    · exact (ih ⟨w, hw, ho⟩).trans (countNot_tail_le g gs)

lemma countNot_one (gs : List Gate)
    (hu : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j)
    (he : ∃ g ∈ gs, g.op = GateOp.not) : countNot gs = 1 := by
  have h1 := countNot_le_one gs hu
  have h2 := countNot_pos gs he
  omega

lemma ex_live_minimal {T : ℕ} (gs : List Gate) (w : List ℕ) (S : Set ℕ)
    (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (hm : m ∈ S)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hT : ∃ i, (ex m gs w).getD i 0 = T)
    (hmin : ∀ k < gs.length, ¬ Sol Z0 m T k S) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length (countNot gs) S0 :=
  (ex_solD m gs w S hw h0 hm hg hT).live_minimal hmin

lemma ex_live_one_minimal {T : ℕ} (gs : List Gate) (w : List ℕ) (S : Set ℕ)
    (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (hm : m ∈ S)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hT : ∃ i, (ex m gs w).getD i 0 = T)
    (hmin : ∀ k < gs.length, ¬ Sol Z0 m T k S)
    (hu : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j)
    (he : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length 1 S0 := by
  simpa [countNot_one gs hu he] using ex_live_minimal m gs w S hw h0 hm hg hT hmin

end counted

lemma bridgeD (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = f y) :
    SolD Z0 (mz 0) (tz 0) D.size (countNot D.gates) (C (mz 0) (WZ [] 0)) := by
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
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
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
  exact ex_solD (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩

lemma circuit_live13_one (gates : List Gate) (o : ℕ)
    (hD : FanInTwo ⟨gates, o⟩)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (he : ∃ g ∈ gates, g.op = GateOp.not) (hlen : gates.length = 13) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧
      Live Z0 (mz 0) (tz 0) 13 1 S0 := by
  have hb := bridgeD ⟨gates, o⟩ hD hf
  change SolD Z0 (mz 0) (tz 0) gates.length (countNot gates) (C (mz 0) (WZ [] 0)) at hb
  have hmin : ∀ k < gates.length, ¬ Sol Z0 (mz 0) (tz 0) k (C (mz 0) (WZ [] 0)) := by
    intro k hk
    exact root13 k (by omega)
  have hl := hb.live_minimal hmin
  simpa only [countNot_one gates hu he, hlen] using hl

lemma circuit_live_one_small (gates : List Gate) (o : ℕ)
    (hD : FanInTwo ⟨gates, o⟩)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (he : ∃ g ∈ gates, g.op = GateOp.not) (hsmall : gates.length < 14) :
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧
      Live Z0 (mz 0) (tz 0) 13 1 S0 := by
  have hl := lower13 ⟨gates, o⟩ hD hf
  change 13 ≤ gates.length at hl
  exact circuit_live13_one gates o hD hf hu he (by omega)

end PEqualNP.Outside.L_meta_10760_aux
