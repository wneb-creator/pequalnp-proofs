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

end PEqualNP.Outside.L_meta_4930
