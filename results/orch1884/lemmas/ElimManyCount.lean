import PEqualNP.MetaComplexity.Helpers.Elim

namespace PEqualNP.Outside.L_meta_1884.ElimManyCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

def reads (K : Finset Nat) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (i ∈ K)

def constant (K : Finset Nat) (e : List Stat) : Prop :=
  ∀ k ∈ K, k < e.length ∧ ∃ b, e.getD k (Stat.const false) = Stat.const b

lemma constants_step (n : Nat) (K : Finset Nat) (acc : List Stat × List Gate)
    (h : constant K acc.1) (g : Gate) : constant K (elimStep n acc g).1 := by
  intro k hk
  obtain ⟨hkl, b, hb⟩ := h k hk
  refine ⟨by simp [elimStep]; omega, b, ?_⟩
  simp only [elimStep]
  rw [getD_snoc_ne _ _ _ _ (by omega)]
  exact hb

lemma read_step_free (n : Nat) (K : Finset Nat) (acc : List Stat × List Gate)
    (h : constant K acc.1) (g : Gate) (hg : NOk g) (hr : reads K g = true) :
    (elimStep n acc g).2.length = acc.2.length := by
  obtain ⟨k, hkg, hk⟩ := List.any_eq_true.mp hr
  obtain ⟨_, b, hb⟩ := h k (of_decide_eq_true hk)
  have hn : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro hop; simpa using hg.2 hop
    · exact ⟨b, List.mem_map.mpr ⟨k, hkg, hb⟩⟩
  simp only [elimStep, List.length_append]
  rw [hn]
  simp

lemma step_length (n : Nat) (acc : List Stat × List Gate) (g : Gate) :
    (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
  have h := toList_length_le (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
  simp only [elimStep, List.length_append]
  omega

theorem count_readers (n : Nat) (K : Finset Nat) (gs : List Gate)
    (acc : List Stat × List Gate) (hg : ∀ g ∈ gs, NOk g)
    (hc : constant K acc.1) :
    (elim n gs acc).2.length + gs.countP (reads K) ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have hi := ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (constants_step n K acc hc g)
    change (elim n gs (elimStep n acc g)).2.length +
      (g :: gs).countP (reads K) ≤ acc.2.length + (g :: gs).length
    cases hr : reads K g
    · have hs := step_length n acc g
      simp only [List.countP_cons, hr, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      omega
    · have hs := read_step_free n K acc hc g (hg g List.mem_cons_self) hr
      simp only [List.countP_cons, hr, ↓reduceIte, List.length_cons]
      omega

lemma status_length (n : Nat) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep]
    omega

lemma constants_preserved (n : Nat) (K : Finset Nat) (gs : List Gate)
    (acc : List Stat × List Gate) (hc : constant K acc.1) :
    constant K (elim n gs acc).1 := by
  intro k hk
  obtain ⟨hkl, b, hb⟩ := hc k hk
  refine ⟨by rw [status_length]; omega, b, ?_⟩
  rw [elim_getD n k _ gs acc hkl]
  exact hb

theorem constant_step_count (n : Nat) (K : Finset Nat) (pre post : List Gate)
    (acc : List Stat × List Gate) (hp : ∀ g ∈ pre, NOk g)
    (hs : ∀ g ∈ post, NOk g) (hc : constant K acc.1)
    (g : Gate) (b : Bool)
    (hstep : elimStep n (elim n pre acc) g =
      ((elim n pre acc).1 ++ [Stat.const b], (elim n pre acc).2)) :
    let q := acc.1.length + pre.length
    let result := elim n (pre ++ g :: post) acc
    result.2.length + pre.countP (reads K) + post.countP (reads (insert q K)) + 1 ≤
      acc.2.length + (pre ++ g :: post).length := by
  dsimp only
  let mid := elim n pre acc
  have hml : mid.1.length = acc.1.length + pre.length := status_length n pre acc
  have hmc : constant K mid.1 := constants_preserved n K pre acc hc
  have hnext : elimStep n mid g = (mid.1 ++ [Stat.const b], mid.2) := hstep
  have hnew : constant (insert (acc.1.length + pre.length) K)
      (mid.1 ++ [Stat.const b]) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · refine ⟨by simp [hml], b, ?_⟩
      exact getD_snoc_len _ _ _ _ hml
    · obtain ⟨hkl, b, hb⟩ := hmc k hk
      refine ⟨by simp; omega, b, ?_⟩
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hb
  have hfirst := count_readers n K pre acc hp hc
  have hlast := count_readers n (insert (acc.1.length + pre.length) K) post
    (mid.1 ++ [Stat.const b], mid.2) hs hnew
  have heq : elim n (pre ++ g :: post) acc =
      elim n post (mid.1 ++ [Stat.const b], mid.2) := by
    simp only [elim, List.foldl_append, List.foldl_cons]
    change post.foldl (elimStep n) (elimStep n mid g) = _
    rw [hnext]
  rw [heq]
  simp only [List.length_append, List.length_cons]
  dsimp only [mid] at hlast ⊢
  omega

theorem forced_true_count (n : Nat) (K : Finset Nat) (pre post : List Gate)
    (acc : List Stat × List Gate) (hp : ∀ g ∈ pre, NOk g)
    (hs : ∀ g ∈ post, NOk g) (hc : constant K acc.1) :
    let q := acc.1.length + pre.length
    let result := elim n (pre ++ ⟨GateOp.and, []⟩ :: post) acc
    result.2.length + pre.countP (reads K) + post.countP (reads (insert q K)) + 1 ≤
      acc.2.length + (pre ++ ⟨GateOp.and, []⟩ :: post).length := by
  apply constant_step_count n K pre post acc hp hs hc ⟨GateOp.and, []⟩ true
  simp [elimStep, simplify, simpAnd]

end PEqualNP.Outside.L_meta_1884.ElimManyCount
