import PEqualNP.Library.LRAT.Link2
import PEqualNP.Defs.LratEncoding

/-!
# Cube and conquer for the AND/OR lower rows

1. The library's definitions are the root's (`PEqualNP.Defs.LratEncoding`): each is proved equal
   by `rfl` (`lib_*_eq`), so a shard stated on the root names is the library's statement.
2. Covering (`enc2_cover`): an assignment satisfying `enc2 n s g rows` (with `s > 0`) satisfies
   `enc2Cube n s k` for some `k < enc2CubeCount n s`: the cube is read off the at-least-one
   clauses of `enc2` for the first source (`fSrcAlo`) and the operation (`fOp`) of gate `s - 1`.
3. Combination (`lower_of_cubes`): if every piece `enc2 n s (rowFun n f) rows ++ enc2Cube n s k`,
   `k < enc2CubeCount n s`, is unsatisfiable, every circuit of AND and OR gates of fan-in at most
   two computing `f` has at least `s + 1` gates.
-/

namespace PEqualNP.Library.LRAT.Cube

open PEqualNP.Library.LRAT


/-! ## The library definitions are the root's -/

theorem lib_litVal_eq : @PEqualNP.Library.LRAT.litVal = @PEqualNP.Defs.LratEncoding.litVal := rfl
theorem lib_ClauseSat_eq :
    @PEqualNP.Library.LRAT.ClauseSat = @PEqualNP.Defs.LratEncoding.ClauseSat := rfl
theorem lib_FormulaSat_eq :
    @PEqualNP.Library.LRAT.FormulaSat = @PEqualNP.Defs.LratEncoding.FormulaSat := rfl
theorem lib_rowFun_eq : @Link.rowFun = @PEqualNP.Defs.LratEncoding.rowFun := rfl
theorem lib_wd_eq : @Link.wd = @PEqualNP.Defs.LratEncoding.wd := rfl
theorem lib_ix_eq : @Link.ix = @PEqualNP.Defs.LratEncoding.ix := rfl
theorem lib_P_eq : @Link.P = @PEqualNP.Defs.LratEncoding.P := rfl
theorem lib_Q_eq : @Link.Q = @PEqualNP.Defs.LratEncoding.Q := rfl
theorem lib_L_eq : @Link.L = @PEqualNP.Defs.LratEncoding.L := rfl
theorem lib_fOp_eq : @Link.fOp = @PEqualNP.Defs.LratEncoding.fOp := rfl
theorem lib_fSrcAlo_eq : @Link.fSrcAlo = @PEqualNP.Defs.LratEncoding.fSrcAlo := rfl
theorem lib_srcEq_eq : @Link.srcEq = @PEqualNP.Defs.LratEncoding.srcEq := rfl
theorem lib_fSrcEq_eq : @Link.fSrcEq = @PEqualNP.Defs.LratEncoding.fSrcEq := rfl
theorem lib_gateCl_eq : @Link.gateCl = @PEqualNP.Defs.LratEncoding.gateCl := rfl
theorem lib_fGate_eq : @Link.fGate = @PEqualNP.Defs.LratEncoding.fGate := rfl
theorem lib_fOutAlo_eq : @Link.fOutAlo = @PEqualNP.Defs.LratEncoding.fOutAlo := rfl
theorem lib_outEq_eq : @Link.outEq = @PEqualNP.Defs.LratEncoding.outEq := rfl
theorem lib_fOutEq_eq : @Link.fOutEq = @PEqualNP.Defs.LratEncoding.fOutEq := rfl
theorem lib_fOut_eq : @Link.fOut = @PEqualNP.Defs.LratEncoding.fOut := rfl
theorem lib_fPad_eq : @Link.fPad = @PEqualNP.Defs.LratEncoding.fPad := rfl
theorem lib_fPre_eq : @Link.fPre = @PEqualNP.Defs.LratEncoding.fPre := rfl
theorem lib_fPadRd_eq : @Link.fPadRd = @PEqualNP.Defs.LratEncoding.fPadRd := rfl
theorem lib_fOrd_eq : @Link.fOrd = @PEqualNP.Defs.LratEncoding.fOrd := rfl
theorem lib_fUsed_eq : @Link.fUsed = @PEqualNP.Defs.LratEncoding.fUsed := rfl
theorem lib_enc_eq : @Link.enc = @PEqualNP.Defs.LratEncoding.enc := rfl
theorem lib_lexBase_eq : @Link.lexBase = @PEqualNP.Defs.LratEncoding.lexBase := rfl
theorem lib_fLex_eq : @Link.fLex = @PEqualNP.Defs.LratEncoding.fLex := rfl
theorem lib_enc2_eq : @Link.enc2 = @PEqualNP.Defs.LratEncoding.enc2 := rfl

/-! ## Covering -/

open PEqualNP.Defs.LratEncoding in
/-- Every assignment satisfying `enc2 n s g rows` (with `s > 0`) satisfies one of the cubes
`enc2Cube n s k`, `k < enc2CubeCount n s`. -/
theorem enc2_cover_asg {n s : Nat} (hs : 0 < s) {g : Nat → Bool} {rows : List Nat}
    {a : Nat → Bool} (ha : ∀ c ∈ enc2 n s g rows, ClauseSat a c) :
    ∃ k < enc2CubeCount n s, ∀ c ∈ enc2Cube n s k, ClauseSat a c := by
  have hsrc : ((List.range (n + (s - 1) + 1)).map fun k => PEqualNP.Defs.LratEncoding.P (ix n s 1 (s - 1) k)) ∈
      enc2 n s g rows := by
    have h1 : ((List.range (n + (s - 1) + 1)).map fun k =>
        PEqualNP.Defs.LratEncoding.P (ix n s 1 (s - 1) k)) ∈ fSrcAlo n s := by
      unfold fSrcAlo
      exact List.mem_flatMap.2 ⟨1, by simp, List.mem_map.2 ⟨s - 1, List.mem_range.2 (by omega), rfl⟩⟩
    simp only [enc2, enc, List.mem_append, h1, true_or, or_true]
  have hop : [PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 0),
      PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 1),
      PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 2)] ∈ enc2 n s g rows := by
    have h1 : [PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 0),
        PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 1),
        PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) 2)] ∈ fOp n s := by
      unfold fOp
      exact List.mem_map.2 ⟨s - 1, List.mem_range.2 (by omega), rfl⟩
    simp only [enc2, enc, List.mem_append, h1, true_or, or_true]
  obtain ⟨l1, hl1, hv1⟩ := ha _ hsrc
  obtain ⟨l2, hl2, hv2⟩ := ha _ hop
  simp only [List.mem_map, List.mem_range] at hl1
  obtain ⟨x, hx, rfl⟩ := hl1
  have ht : ∃ t < 3, l2 = PEqualNP.Defs.LratEncoding.P (ix n s 0 (s - 1) t) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl2
    rcases hl2 with h | h | h
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
    · exact ⟨2, by omega, h⟩
  obtain ⟨t, htl, rfl⟩ := ht
  have hpos : 0 < n + s := by omega
  refine ⟨t * (n + s) + x, ?_, ?_⟩
  · unfold enc2CubeCount
    have : t * (n + s) + x < (t + 1) * (n + s) := by rw [Nat.succ_mul]; omega
    have h3 : (t + 1) * (n + s) ≤ 3 * (n + s) := Nat.mul_le_mul_right _ htl
    omega
  · have hm : (t * (n + s) + x) % (n + s) = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hd : (t * (n + s) + x) / (n + s) = t := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    intro c hc
    simp only [enc2Cube, hm, hd, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, hv1⟩
    · exact ⟨_, List.mem_singleton_self _, hv2⟩

open PEqualNP.Defs.LratEncoding in
/-- The covering lemma: if `enc2 n s g rows` is satisfiable (`s > 0`), so is one of its pieces
`enc2 n s g rows ++ enc2Cube n s k` with `k < enc2CubeCount n s`. -/
theorem enc2_cover (n s : Nat) (hs : 0 < s) (g : Nat → Bool) (rows : List Nat)
    (h : FormulaSat (enc2 n s g rows)) :
    ∃ k < enc2CubeCount n s, FormulaSat (enc2 n s g rows ++ enc2Cube n s k) := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨k, hk, hc⟩ := enc2_cover_asg hs ha
  refine ⟨k, hk, a, fun c hc' => ?_⟩
  rcases List.mem_append.1 hc' with h1 | h1
  · exact ha c h1
  · exact hc c h1

/-! ## Combination -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
/-- If every piece `enc2 n s (rowFun n f) rows ++ enc2Cube n s k`, `k < enc2CubeCount n s`, is
unsatisfiable (`s > 0`, rows below `2 ^ n`), every circuit of AND and OR gates of fan-in at most
two computing `f` on `n` inputs has at least `s + 1` gates. -/
theorem lower_of_cubes (n s : Nat) (hs : 0 < s) (f : (Fin n → Bool) → Bool) (rows : List Nat)
    (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ∀ k < enc2CubeCount n s, ¬ FormulaSat (enc2 n s (rowFun n f) rows ++ enc2Cube n s k)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  refine Link.lower_of_unsat2 n s f rows hrows fun h => ?_
  obtain ⟨k, hk, hk'⟩ := enc2_cover n s hs (rowFun n f) rows h
  exact hU k hk hk'

end PEqualNP.Library.LRAT.Cube
