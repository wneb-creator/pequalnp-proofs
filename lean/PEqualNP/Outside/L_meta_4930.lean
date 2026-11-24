import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_4930

abbrev Gate := Bool × ℕ × ℕ

def valid (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i : Fin gs.length, (gs.getD i.val (false, 0, 0)).2.1 <
    (gs.getD i.val (false, 0, 0)).2.2 ∧
    (gs.getD i.val (false, 0, 0)).2.2 < n + i.val

def run (xs : List (BitVec 58)) (gs : List Gate) : List (BitVec 58) :=
  gs.foldl (fun xs g => xs ++ [if g.1 = true then
    xs.getD g.2.1 0 &&& xs.getD g.2.2 0 else
    xs.getD g.2.1 0 ||| xs.getD g.2.2 0]) xs

lemma valid_append {n : ℕ} {p q : List Gate}
    (hp : valid n p) (hq : valid (n + p.length) q) : valid n (p ++ q) := by
  intro i
  by_cases h : i.val < p.length
  · rw [List.getD_append p q (false, 0, 0) i.val h]
    exact hp ⟨i.val, h⟩
  · have hi := i.isLt
    simp only [List.length_append] at hi
    have hle : p.length ≤ i.val := by omega
    rw [List.getD_append_right p q (false, 0, 0) i.val hle]
    have hr := hq ⟨i.val - p.length, by omega⟩
    dsimp only at hr
    exact ⟨hr.1, by omega⟩

lemma run_append (xs : List (BitVec 58)) (p q : List Gate) :
    run xs (p ++ q) = run (run xs p) q := by
  simp only [run, List.foldl_append]

lemma witness_of_suffix (xs : List (BitVec 58)) (target : BitVec 58)
    (p q : List Gate) (hlen : p.length + q.length = 26)
    (hp : valid 14 p) (hq : valid (14 + p.length) q)
    (heval : target ∈ run (run xs p) q) :
    ∃ gs : List Gate, gs.length = 26 ∧ valid 14 gs ∧ target ∈ run xs gs := by
  refine ⟨p ++ q, ?_, valid_append hp hq, ?_⟩
  · simpa only [List.length_append] using hlen
  · simpa only [run_append] using heval

lemma mem_run {xs : List (BitVec 58)} {target : BitVec 58}
    (gs : List Gate) (h : target ∈ xs) : target ∈ run xs gs := by
  induction gs generalizing xs with
  | nil => simpa [run] using h
  | cons g gs ih =>
    simp only [run, List.foldl_cons]
    apply ih
    exact List.mem_append_left _ h

lemma valid_padding {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    valid n (List.replicate k (false, 0, 1)) := by
  intro i
  rw [List.getD_eq_getElem _ _ i.isLt]
  simp only [List.getElem_replicate]
  omega

lemma witness_of_short (xs : List (BitVec 58)) (target : BitVec 58)
    (p : List Gate) {n k : ℕ} (hn : 2 ≤ n) (hlen : p.length ≤ k)
    (hp : valid n p) (heval : target ∈ run xs p) :
    ∃ gs : List Gate, gs.length = k ∧ valid n gs ∧ target ∈ run xs gs := by
  refine ⟨p ++ List.replicate (k - p.length) (false, 0, 1), ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · exact valid_append hp (valid_padding (by omega) _)
  · rw [run_append]
    exact mem_run _ heval

lemma witness_of_short26 (xs : List (BitVec 58)) (target : BitVec 58)
    (p : List Gate) (hlen : p.length ≤ 26)
    (hp : valid 14 p) (heval : target ∈ run xs p) :
    ∃ gs : List Gate, gs.length = 26 ∧ valid 14 gs ∧ target ∈ run xs gs := by
  exact witness_of_short xs target p (by decide) hlen hp heval

lemma run_length (xs : List (BitVec 58)) (gs : List Gate) :
    (run xs gs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run (xs ++ [if g.1 = true then
      xs.getD g.2.1 0 &&& xs.getD g.2.2 0 else
      xs.getD g.2.1 0 ||| xs.getD g.2.2 0]) gs).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_getD_old (xs : List (BitVec 58)) (gs : List Gate) (a : ℕ)
    (ha : a < xs.length) : (run xs gs).getD a 0 = xs.getD a 0 := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run (xs ++ [if g.1 = true then
      xs.getD g.2.1 0 &&& xs.getD g.2.2 0 else
      xs.getD g.2.1 0 ||| xs.getD g.2.2 0]) gs).getD a 0 = _
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ ha

lemma valid_singleton {n a b : ℕ} (op : Bool) (hab : a < b) (hbn : b < n) :
    valid n [(op, a, b)] := by
  intro i
  have hi : i.val = 0 := by have := i.isLt; simp only [List.length_singleton] at this; omega
  rw [hi]
  exact ⟨hab, hbn⟩

lemma getD_last_append_singleton (xs : List (BitVec 58)) (z : BitVec 58) :
    (xs ++ [z]).getD ((xs ++ [z]).length - 1) 0 = z := by
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp only [Nat.sub_self]
  rfl

lemma pad_absorbing_last (xs : List (BitVec 58)) (z : BitVec 58)
    (op : Bool) (a k : ℕ) (ha : a < xs.length - 1)
    (hz : xs.getD (xs.length - 1) 0 = z)
    (habs : (if op = true then xs.getD a 0 &&& z else xs.getD a 0 ||| z) = z) :
    ∃ q : List Gate, q.length = k ∧ valid xs.length q ∧
      (run xs q).getD ((run xs q).length - 1) 0 = z := by
  induction k with
  | zero =>
    refine ⟨[], rfl, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · exact hz
  | succ k ih =>
    obtain ⟨q, hq, hv, hzq⟩ := ih
    have hlen : (run xs q).length = xs.length + k := by rw [run_length, hq]
    have hzq' : (run xs q).getD (xs.length + k - 1) 0 = z := by
      simpa only [hlen] using hzq
    have hinput : (run xs q).getD a 0 = xs.getD a 0 :=
      run_getD_old xs q a (by omega)
    have hstep : run (run xs q) [(op, a, xs.length + k - 1)] = run xs q ++ [z] := by
      change run xs q ++ [if op = true then
        (run xs q).getD a 0 &&& (run xs q).getD (xs.length + k - 1) 0 else
        (run xs q).getD a 0 ||| (run xs q).getD (xs.length + k - 1) 0] = _
      rw [hinput, hzq', habs]
    refine ⟨q ++ [(op, a, xs.length + k - 1)], ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, hq]
    · exact valid_append hv (valid_singleton op (by omega) (by omega))
    · rw [run_append, hstep]
      exact getD_last_append_singleton _ _

lemma witness_last_of_short (xs : List (BitVec 58)) (z : BitVec 58)
    (p : List Gate) {n k : ℕ} (hxs : xs.length = n) (hlen : p.length ≤ k)
    (hp : valid n p) (op : Bool) (a : ℕ)
    (ha : a < (run xs p).length - 1)
    (hz : (run xs p).getD ((run xs p).length - 1) 0 = z)
    (habs : (if op = true then (run xs p).getD a 0 &&& z
      else (run xs p).getD a 0 ||| z) = z) :
    ∃ gs : List Gate, gs.length = k ∧ valid n gs ∧
      (run xs gs).getD ((run xs gs).length - 1) 0 = z := by
  obtain ⟨q, hq, hv, hzq⟩ := pad_absorbing_last (run xs p) z op a
    (k - p.length) ha hz habs
  refine ⟨p ++ q, ?_, valid_append hp ?_, ?_⟩
  · simp only [List.length_append, hq]
    omega
  · simpa only [run_length, hxs] using hv
  · simpa only [run_append] using hzq

lemma valid_last {n : ℕ} {p : List Gate} {op : Bool} {a b : ℕ}
    (h : valid n (p ++ [(op, a, b)])) : a < b ∧ b < n + p.length := by
  have hv := h ⟨p.length, by simp only [List.length_append, List.length_singleton]; omega⟩
  dsimp only at hv
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)] at hv
  simp only [Nat.sub_self] at hv
  exact hv

lemma gate_absorbs_left (op : Bool) (u v : BitVec 58) :
    (if op = true then u &&& (if op = true then u &&& v else u ||| v)
      else u ||| (if op = true then u &&& v else u ||| v)) =
      (if op = true then u &&& v else u ||| v) := by
  cases op
  · simp only [Bool.false_eq_true, ite_false, ← BitVec.or_assoc, BitVec.or_self]
  · simp only [ite_true, ← BitVec.and_assoc, BitVec.and_self]

lemma witness_last_of_short_final_gate (xs : List (BitVec 58)) (z : BitVec 58)
    (p : List Gate) (op : Bool) (a b : ℕ) {n k : ℕ}
    (hxs : xs.length = n) (hlen : (p ++ [(op, a, b)]).length ≤ k)
    (hp : valid n (p ++ [(op, a, b)]))
    (hz : (run xs (p ++ [(op, a, b)])).getD
      ((run xs (p ++ [(op, a, b)])).length - 1) 0 = z) :
    ∃ gs : List Gate, gs.length = k ∧ valid n gs ∧
      (run xs gs).getD ((run xs gs).length - 1) 0 = z := by
  have hv := valid_last hp
  have hsize : (run xs p).length = n + p.length := by rw [run_length, hxs]
  have ha : a < (run xs p).length := by omega
  have hrun : run xs (p ++ [(op, a, b)]) = run xs p ++
      [if op = true then (run xs p).getD a 0 &&& (run xs p).getD b 0
        else (run xs p).getD a 0 ||| (run xs p).getD b 0] := by
    rw [run_append]
    rfl
  have heval : (if op = true then (run xs p).getD a 0 &&& (run xs p).getD b 0
      else (run xs p).getD a 0 ||| (run xs p).getD b 0) = z := by
    rw [hrun, getD_last_append_singleton] at hz
    exact hz
  have hfinal : run xs (p ++ [(op, a, b)]) = run xs p ++ [z] := by
    rw [hrun, heval]
  apply witness_last_of_short xs z (p ++ [(op, a, b)]) hxs hlen hp op a
  · rw [hfinal]
    simpa only [List.length_append, List.length_singleton, Nat.add_sub_cancel] using ha
  · exact hz
  · rw [hfinal, List.getD_append _ _ _ _ ha, ← heval]
    exact gate_absorbs_left op _ _

lemma valid_take {n : ℕ} {p : List Gate} (hp : valid n p) (k : ℕ) :
    valid n (p.take k) := by
  intro i
  have hi : i.val < p.length := by have := i.isLt; simp only [List.length_take] at this; omega
  have htake : (p.take k).getD i.val (false,0,0) = p.getD i.val (false,0,0) := by
    rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ hi]
    simp only [List.getElem_take]
  rw [htake]
  exact hp ⟨i.val, hi⟩

lemma last_prefix (xs : List (BitVec 58)) (p : List Gate) (z : BitVec 58)
    (hp : valid xs.length p) (hz : z ∈ run xs p) (hnot : z ∉ xs) :
    ∃ q : List Gate, 0 < q.length ∧ q.length ≤ p.length ∧ valid xs.length q ∧
      (run xs q).getD (xs.length + q.length - 1) 0 = z := by
  obtain ⟨⟨i, hiLt⟩, hi⟩ := List.get_of_mem hz
  have hget : (run xs p).getD i 0 = z := by
    rw [List.getD_eq_get _ _ ⟨i, hiLt⟩]
    exact hi
  have ilt : i < xs.length + p.length := by simpa only [run_length] using hiLt
  have hge : xs.length ≤ i := by
    by_cases hlt : i < xs.length
    · exfalso
      have hzold : xs.getD i 0 = z := by rw [← run_getD_old xs p i hlt]; exact hget
      apply hnot
      rw [← hzold, List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem _
    · omega
  let k := i + 1 - xs.length
  have hk : 0 < k ∧ k ≤ p.length := by dsimp [k]; omega
  have hlen : (p.take k).length = k := by simp only [List.length_take, Nat.min_eq_left hk.2]
  have hind : xs.length + (p.take k).length - 1 = i := by rw [hlen]; dsimp [k]; omega
  refine ⟨p.take k, by omega, by omega, valid_take hp k, ?_⟩
  rw [hind]
  have hidx : i < (run xs (p.take k)).length := by rw [run_length, hlen]; dsimp [k]; omega
  have heq : run xs p = run (run xs (p.take k)) (p.drop k) := by
    rw [← run_append, List.take_append_drop]
  rw [heq, run_getD_old _ _ _ hidx] at hget
  exact hget

lemma witness_last_of_membership (xs : List (BitVec 58)) (p : List Gate)
    (z : BitVec 58) (k : ℕ) (hp : valid xs.length p) (hlen : p.length ≤ k)
    (hz : z ∈ run xs p) (hnot : z ∉ xs) :
    ∃ gs : List Gate, gs.length = k ∧ valid xs.length gs ∧
      (run xs gs).getD (xs.length + k - 1) 0 = z := by
  obtain ⟨q, hpos, hle, hv, hzq⟩ := last_prefix xs p z hp hz hnot
  have hqne : q ≠ [] := by intro hq; rw [hq] at hpos; exact Nat.not_lt_zero _ hpos
  obtain ⟨op, a, b, hg⟩ : ∃ op a b, q.getLast hqne = (op, a, b) :=
    ⟨(q.getLast hqne).1, (q.getLast hqne).2.1, (q.getLast hqne).2.2, rfl⟩
  have heq : q.dropLast ++ [(op, a, b)] = q := by
    rw [← hg]
    exact List.dropLast_concat_getLast hqne
  have hlenq : (q.dropLast ++ [(op, a, b)]).length ≤ k := by rw [heq]; omega
  have hvq : valid xs.length (q.dropLast ++ [(op, a, b)]) := by rw [heq]; exact hv
  have hlast : (run xs (q.dropLast ++ [(op, a, b)])).getD
      ((run xs (q.dropLast ++ [(op, a, b)])).length - 1) 0 = z := by
    rw [heq, run_length]
    exact hzq
  obtain ⟨gs, hgs, hvgs, hzgs⟩ := witness_last_of_short_final_gate xs z q.dropLast
    op a b rfl hlenq hvq hlast
  refine ⟨gs, hgs, hvgs, ?_⟩
  simpa only [run_length, hgs] using hzgs

end PEqualNP.Outside.L_meta_4930
