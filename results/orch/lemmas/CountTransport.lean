import CertificateBound

namespace PEqualNP.Outside.L_meta_2592_aux.Certificate.LinkN

open PEqualNP.CircuitLowerBounds

def gateNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

lemma code_not_only (n j : ℕ) (g : Gate) (h : (code n g j).1 = 3) : g.op = GateOp.not := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp_all [code]

lemma sum_gate_not (gs : List Gate) :
    (∑ j ∈ Finset.range gs.length,
      if gateNot (gs.getD j ⟨.and, []⟩) then 1 else 0) =
        gs.countP gateNot := by
  classical
  induction gs with
  | nil => simp
  | cons g gs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, List.countP_cons, ih]

lemma modelNotCount_ofCirc_le (n s : ℕ) (C : Circuit) (hs : C.size ≤ s) :
    modelNotCount s (ofCirc n s C) ≤ PEqualNP.NotBracket.notCount C := by
  classical
  have hc : C.gates.length ≤ s := hs
  have hb : modelNotCount s (ofCirc n s C) ≤
      ∑ j ∈ Finset.range s,
        if gateNot (C.gates.getD j ⟨.and, []⟩) then 1 else 0 := by
    unfold modelNotCount
    apply Finset.sum_le_sum
    intro j hj
    by_cases hh : (ofCirc n s C).op j = 3
    · have hn := code_not_only n j (gateAt C j) hh
      simp only [gateAt] at hn
      have hg : gateNot (C.gates.getD j ⟨.and, []⟩) = true := by
        unfold gateNot
        rw [hn]
      simp only [hh, hg, ite_true, le_refl]
    · simp [hh]
  have he : (∑ j ∈ Finset.range s,
      if gateNot (C.gates.getD j ⟨.and, []⟩) then 1 else 0) =
      ∑ j ∈ Finset.range C.gates.length,
      if gateNot (C.gates.getD j ⟨.and, []⟩) then 1 else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono hc)
    intro j hj hn
    have hge : C.gates.length ≤ j := by simpa using hn
    rw [List.getD_eq_default _ _ hge]
    rfl
  rw [he, sum_gate_not] at hb
  have heq : C.gates.countP gateNot = PEqualNP.NotBracket.notCount C := by
    rw [List.countP_eq_length_filter]
    unfold PEqualNP.NotBracket.notCount
    apply congrArg List.length
    apply List.filter_congr
    intro g hg
    rcases g with ⟨op, ins⟩
    cases op <;> rfl
  simpa only [heq] using hb

def fNotAtMost (n s k : ℕ) : List (List ℕ) :=
  (((List.range s).sublistsLen (k + 1)).reverse).map fun js =>
    js.map fun j => Q (ix n s 0 j 3)

lemma exists_not_op (s k : ℕ) (M : Model) (hk : modelNotCount s M ≤ k)
    (js : List ℕ) (hjs : js ∈ (List.range s).sublistsLen (k + 1)) :
    ∃ j ∈ js, M.op j ≠ 3 := by
  classical
  obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hjs
  have hnd : js.Nodup := List.nodup_range.sublist hsub
  by_contra! hall
  have hset : js.toFinset ⊆ Finset.range s := by
    intro j hj
    exact Finset.mem_range.mpr (List.mem_range.mp (hsub.subset (List.mem_toFinset.mp hj)))
  have hc : js.toFinset.card ≤ modelNotCount s M := by
    calc
      js.toFinset.card = ∑ j ∈ js.toFinset, if M.op j = 3 then 1 else 0 := by
        symm
        calc
          (∑ j ∈ js.toFinset, if M.op j = 3 then 1 else 0) = ∑ _j ∈ js.toFinset, 1 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [if_pos (hall j (List.mem_toFinset.mp hj))]
          _ = js.toFinset.card := by simp
      _ ≤ modelNotCount s M := by
        unfold modelNotCount
        exact Finset.sum_le_sum_of_subset_of_nonneg hset (fun _ _ _ => Nat.zero_le _)
  rw [List.toFinset_card_of_nodup hnd, hlen] at hc
  omega

lemma fNotAtMost_sat (n s k : ℕ) (M : Model) (hk : modelNotCount s M ≤ k) :
    ∀ c ∈ fNotAtMost n s k, ClauseSat (val n s M) c := by
  intro c hc
  obtain ⟨js, hjs, rfl⟩ := List.mem_map.mp hc
  have hjs' := List.mem_reverse.mp hjs
  obtain ⟨j, hj, hn⟩ := exists_not_op s k M hk js hjs'
  have hsub := (List.mem_sublistsLen.mp hjs').1
  have hlt : j < s := List.mem_range.mp (hsub.subset hj)
  refine ⟨Q (ix n s 0 j 3), List.mem_map.mpr ⟨j, hj, rfl⟩, ?_⟩
  rw [litVal_Q, v_op M (by omega) (wd_lt1 (by omega))]
  simp [hn]


def enc2NotAtMost (n s k : ℕ) (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  enc2 n s g rows ++ fNotAtMost n s k

lemma link2_notBound (n s k : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hsz : C.size ≤ s) (hk : PEqualNP.NotBracket.notCount C ≤ k)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2NotAtMost n s k (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  have hb := (modelNotCount_ofCirc_le n s C hsz).trans hk
  obtain ⟨M, hM, hnf, hlx, hcount⟩ := exists_nf2_notBound ⟨_, hv, hb⟩
  refine ⟨val n s M, ?_⟩
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact enc2_sat hrows hM hnf hlx c hc
  · exact fNotAtMost_sat n s k M hcount c hc

lemma lower_of_unsat2_notBound (n s k : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ¬ FormulaSat (enc2NotAtMost n s k (rowFun n f) rows)) :
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.NotBracket.notCount C ≤ k →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) → s + 1 ≤ C.size := by
  intro C hC hk hev
  by_contra h
  exact hU (link2_notBound n s k f rows hrows C hC (by omega) hk hev)

end PEqualNP.Outside.L_meta_2592_aux.Certificate.LinkN
