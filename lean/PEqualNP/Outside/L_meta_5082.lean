import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5082

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]


def rho (N j : ℕ) (i : ℕ) : ℕ := if i < N then i else if i = N then j else i - 1

def rel (N j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho N j)⟩

lemma getD_snoc (w : List Bool) (a : Bool) (k : ℕ) :
    (w ++ [a]).getD k false = if k < w.length then w.getD k false else if k = w.length then a else false := by
  by_cases h1 : k < w.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : k = w.length
    · rw [if_pos h2, h2]
      simp
    · rw [if_neg h2]
      apply List.getD_eq_default
      rw [List.length_append]
      simp
      omega

lemma main (N j : ℕ) (hj : j < N) : ∀ (gs : List Gate) (w8 w1 : List Bool),
    w1.length = w8.length + 1 → N ≤ w8.length →
    (∀ i, w8.getD (rho N j i) false = w1.getD i false) →
    ∀ i, (wiresFrom (gs.map (rel N j)) w8).getD (rho N j i) false = (wiresFrom gs w1).getD i false := by
  intro gs
  induction gs with
  | nil => intro w8 w1 _ _ hinv i; simpa [wiresFrom] using hinv i
  | cons g gs ih =>
    intro w8 w1 hlen hN hinv
    have hval : (rel N j g).op.eval ((rel N j g).inputs.map fun i => w8.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      simp only [rel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hinv i
    have e8 : wiresFrom ((g :: gs).map (rel N j)) w8 = wiresFrom (gs.map (rel N j))
        (w8 ++ [(rel N j g).op.eval ((rel N j g).inputs.map fun i => w8.getD i false)]) := rfl
    have e1 : wiresFrom (g :: gs) w1 = wiresFrom gs
        (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]) := rfl
    rw [e8, e1, hval]
    apply ih
    · simp [hlen]
    · simp; omega
    · intro i
      rw [getD_snoc, getD_snoc, hlen]
      have hi := hinv i
      unfold rho at hi ⊢
      by_cases c1 : i < N
      · simp only [c1, if_true] at hi ⊢
        rw [if_pos (by omega), if_pos (by omega)]
        exact hi
      · by_cases c2 : i = N
        · simp only [c1, c2, if_false, if_true, lt_irrefl] at hi ⊢
          rw [if_pos (by omega), if_pos (by omega)]
          exact hi
        · simp only [c1, c2, if_false] at hi ⊢
          by_cases c3 : i < w8.length + 1
          · rw [if_pos (by omega), if_pos c3]
            exact hi
          · rw [if_neg (by omega), if_neg c3]
            by_cases c4 : i = w8.length + 1
            · rw [if_pos (by omega), if_pos c4]
            · rw [if_neg (by omega), if_neg c4]

end PEqualNP.Outside.L_meta_5082

theorem PEqualNP.Outside.L_meta_5082 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 → x2 < x1.gates.length → x3 < (26 : ℕ) + x2 → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x8 ∧ x8.size < x1.size ∧ ∀ (x9 : List Bool), x9.length = (26 : ℕ) → (x1.wires x9).getD ((26 : ℕ) + x2) Bool.false = (x1.wires x9).getD x3 Bool.false → x8.eval x9 = x1.eval x9 := by
  intro C m j hM hRB hm hj
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    have h1 := (List.take_append_drop m C.gates).symm
    rw [List.drop_eq_getElem_cons hm] at h1
    exact h1
  refine ⟨⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (PEqualNP.Outside.L_meta_5082.rel (26 + m) j),
    PEqualNP.Outside.L_meta_5082.rho (26 + m) j C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hM g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
      have := hM g0 (List.mem_of_mem_drop hg0)
      exact ⟨this.1, by simpa [PEqualNP.Outside.L_meta_5082.rel] using this.2⟩
  · intro k hk i hi
    have hk' : k < m + (C.gates.length - (m + 1)) := by
      simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hm)] using hk
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] at hi
    by_cases c : k < m
    · have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (PEqualNP.Outside.L_meta_5082.rel (26 + m) j))[k]? = C.gates[k]? := by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt c]
      rw [e] at hi
      have := hRB k (by omega) i (by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD] using hi)
      exact this
    · have hk1 : k + 1 < C.gates.length := by omega
      have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (PEqualNP.Outside.L_meta_5082.rel (26 + m) j))[k]? =
          some (PEqualNP.Outside.L_meta_5082.rel (26 + m) j (C.gates[k + 1])) := by
        rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hm), List.getElem?_map, List.getElem?_drop]
        have : m + 1 + (k - m) = k + 1 := by omega
        rw [this, List.getElem?_eq_getElem hk1]
        rfl
      rw [e] at hi
      simp only [Option.getD_some, PEqualNP.Outside.L_meta_5082.rel, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have h0 := hRB (k + 1) hk1 i0 (by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hk1] using hi0)
      unfold PEqualNP.Outside.L_meta_5082.rho
      split_ifs <;> omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_take,
      List.length_map, List.length_drop]
    omega
  · intro x hx heq
    have hPl : (PEqualNP.Outside.L_meta_5082.wiresFrom (C.gates.take m) x).length = 26 + m := by
      rw [PEqualNP.Outside.L_meta_5082.length_wiresFrom, List.length_take, Nat.min_eq_left (Nat.le_of_lt hm), hx]
    have hW1 : C.wires x = PEqualNP.Outside.L_meta_5082.wiresFrom (C.gates.drop (m + 1))
        (PEqualNP.Outside.L_meta_5082.wiresFrom (C.gates.take m) x ++
          [(C.gates[m]).op.eval ((C.gates[m]).inputs.map fun i => (PEqualNP.Outside.L_meta_5082.wiresFrom (C.gates.take m) x).getD i false)]) := by
      show PEqualNP.Outside.L_meta_5082.wiresFrom C.gates x = _
      conv_lhs => rw [hsplit, PEqualNP.Outside.L_meta_5082.wiresFrom_append]
      rfl
    have hW8 : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (PEqualNP.Outside.L_meta_5082.rel (26 + m) j),
        PEqualNP.Outside.L_meta_5082.rho (26 + m) j C.output⟩ x =
        PEqualNP.Outside.L_meta_5082.wiresFrom ((C.gates.drop (m + 1)).map (PEqualNP.Outside.L_meta_5082.rel (26 + m) j)) (PEqualNP.Outside.L_meta_5082.wiresFrom (C.gates.take m) x) :=
      PEqualNP.Outside.L_meta_5082.wiresFrom_append _ _ _
    rw [hW1] at heq
    rw [PEqualNP.Outside.L_meta_5082.getD_wiresFrom_lt _ _ _ (by rw [List.length_append, hPl]; simp),
      PEqualNP.Outside.L_meta_5082.getD_wiresFrom_lt _ _ _ (by rw [List.length_append, hPl]; simp; omega),
      PEqualNP.Outside.L_meta_5082.getD_snoc, PEqualNP.Outside.L_meta_5082.getD_snoc, hPl, if_neg (lt_irrefl _), if_pos rfl, if_pos hj] at heq
    show (PEqualNP.CircuitLowerBounds.Circuit.wires _ x).getD (PEqualNP.Outside.L_meta_5082.rho (26 + m) j C.output) false =
      (C.wires x).getD C.output false
    rw [hW8, hW1]
    apply PEqualNP.Outside.L_meta_5082.main (26 + m) j hj
    · rw [List.length_append]; simp
    · rw [hPl]
    · intro i
      rw [PEqualNP.Outside.L_meta_5082.getD_snoc, hPl]
      unfold PEqualNP.Outside.L_meta_5082.rho
      by_cases c1 : i < 26 + m
      · simp only [c1, if_true]
      · by_cases c2 : i = 26 + m
        · simp only [c1, c2, if_false, if_true, lt_irrefl]
          exact heq.symm
        · simp only [c1, c2, if_false]
          apply List.getD_eq_default
          rw [hPl]; omega
