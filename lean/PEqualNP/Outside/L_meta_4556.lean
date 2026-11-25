import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4556

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def remap (m i : ℕ) : ℕ :=
  if i < 9 then i else if i = 9 then 10 + m else i - 1

lemma remap_wires (m : ℕ) :
    ∀ (gs : List Gate) (acc1 acc2 : List Bool),
      acc1.length = acc2.length + 1 →
      10 ≤ acc2.length →
      acc2.length + gs.length ≤ 10 + m →
      (∀ i < 9, acc1.getD i false = acc2.getD i false) →
      acc1.getD 9 false = false →
      (∀ k, 10 ≤ k → acc1.getD k false = acc2.getD (k - 1) false) →
      let gs' := gs.map (fun g => { op := g.op, inputs := g.inputs.map (remap m) : Gate })
      let r1 := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc1
      let r2 := gs'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc2
      (∀ i < 9, r1.getD i false = r2.getD i false) ∧
      r1.getD 9 false = false ∧
      (∀ k, 10 ≤ k → r1.getD k false = r2.getD (k - 1) false) ∧
      r2.length ≤ 10 + m := by
  intro gs
  induction gs with
  | nil =>
    intro acc1 acc2 _ _ hle hlt h9 hge
    exact ⟨hlt, h9, hge, by simpa using hle⟩
  | cons g rest ih =>
    intro acc1 acc2 hlen h10 hle hlt h9 hge
    have hmap : (g.inputs.map fun i => acc1.getD i false) =
        ((g.inputs.map (remap m)).map fun i => acc2.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, remap]
      by_cases hi9 : i < 9
      · rw [if_pos hi9]; exact hlt i hi9
      · rw [if_neg hi9]
        by_cases hieq : i = 9
        · rw [if_pos hieq, hieq, h9]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp at hle; omega)]; rfl
        · rw [if_neg hieq]
          exact hge i (by omega)
    have hval : g.op.eval (g.inputs.map fun i => acc1.getD i false) =
        g.op.eval ((g.inputs.map (remap m)).map fun i => acc2.getD i false) := by
      rw [hmap]
    have hget_app : ∀ (l : List Bool) (b : Bool) (k : ℕ),
        (l ++ [b]).getD k false =
          if k < l.length then l.getD k false else if k = l.length then b else false := by
      intro l b k
      simp only [List.getD_eq_getElem?_getD]
      by_cases hk : k < l.length
      · rw [if_pos hk, List.getElem?_append_left hk]
      · rw [if_neg hk, List.getElem?_append_right (Nat.le_of_not_lt hk)]
        by_cases hkeq : k = l.length
        · subst hkeq; simp
        · rw [if_neg hkeq]
          rw [List.getElem?_eq_none (by simp; omega)]; rfl
    simp only [List.map_cons, List.foldl_cons]
    apply ih
      (acc1 ++ [g.op.eval (g.inputs.map fun i => acc1.getD i false)])
      (acc2 ++ [g.op.eval ((g.inputs.map (remap m)).map fun i => acc2.getD i false)])
    · simp [hlen]
    · simp; omega
    · simp at hle ⊢; omega
    · intro i hi
      rw [hget_app, hget_app, if_pos (by omega), if_pos (by omega)]
      exact hlt i hi
    · rw [hget_app, if_pos (by omega)]
      exact h9
    · intro k hk
      rw [hget_app, hget_app]
      split_ifs
      · exact hge k hk
      · omega
      · omega
      · omega
      · exact hval
      · omega
      · omega
      · omega
      · rfl

lemma main_proof (x1 : Circuit) (hF2 : FanInTwo x1) (hsz : x1.size ≤ 13) :
    HasCircuitSize 10
      (fun x4 : Fin 10 → Bool => x1.eval (List.ofFn (Fin.init x4) ++ [false, x4 9])) 13 := by
  let m := x1.gates.length
  let C' : Circuit :=
    { gates := x1.gates.map (fun g => { op := g.op, inputs := g.inputs.map (remap m) })
      output := remap m x1.output }
  refine ⟨C', ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    obtain ⟨hop, hlen⟩ := hF2 g0 hg0
    exact ⟨hop, by simpa using hlen⟩
  · simpa [C', Circuit.size] using hsz
  · intro x4
    let acc1 := List.ofFn (Fin.init x4) ++ [false, x4 9]
    let acc2 := List.ofFn x4
    have hres := remap_wires m x1.gates acc1 acc2
      (by simp [acc1, acc2])
      (by simp [acc2])
      (by simp [acc2, m])
      (fun i hi => by
        dsimp only [acc1, acc2]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by simp; omega),
          List.getElem?_ofFn, List.getElem?_ofFn,
          dif_pos hi, dif_pos (by omega : i < 10)]
        rfl)
      (by
        simp only [acc1, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp)]
        simp)
      (fun k hk => by
        simp only [acc1, acc2, List.getD_eq_getElem?_getD]
        by_cases hk10 : k = 10
        · subst hk10
          rw [List.getElem?_append_right (by simp)]
          simp [List.getElem?_ofFn]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    rcases hres with ⟨hlt, h9, hge, hlen2⟩
    change (C'.wires acc2).getD (remap m x1.output) false = (x1.wires acc1).getD x1.output false
    simp only [remap]
    by_cases ho9 : x1.output < 9
    · rw [if_pos ho9]; exact (hlt x1.output ho9).symm
    · rw [if_neg ho9]
      by_cases hoeq : x1.output = 9
      · rw [if_pos hoeq, hoeq]
        dsimp only [Circuit.wires, C']
        rw [h9, List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen2]
        rfl
      · rw [if_neg hoeq]
        exact (hge x1.output (by omega)).symm

end PEqualNP.Outside.L_meta_4556

theorem PEqualNP.Outside.L_meta_4556 :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) (fun (x4 : Fin (10 : ℕ) → Bool) => x1.eval (List.ofFn (Fin.init x4) ++ [Bool.false, x4 (9 : Fin (10 : ℕ))])) (13 : ℕ) := by
  intro x1 hF2 hsz
  exact PEqualNP.Outside.L_meta_4556.main_proof x1 hF2 hsz
