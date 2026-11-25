import PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760
variable {R : ℕ → ℕ}
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

end PEqualNP.Outside.L_meta_10760
