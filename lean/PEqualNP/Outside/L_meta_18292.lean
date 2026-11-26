import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18292
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)]

def legal (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

open Classical in
noncomputable def fixGate (n : ℕ) (g : Gate) : Gate :=
  if g.op = .and then
    if ∀ k ∈ g.inputs, k < n then g else ⟨.or, []⟩
  else ⟨.or, g.inputs.filter (· < n)⟩

theorem fix_spec (n : ℕ) (g : Gate) (hg : legal g) :
    legal (fixGate n g) ∧ (∀ k ∈ (fixGate n g).inputs, k < n) ∧
    ∀ ws : List Bool, ws.length = n → step ws (fixGate n g) = step ws g := by
  rcases hg with ⟨hop, hlen⟩
  rcases hop with ha | ho
  · change g.op = GateOp.and at ha
    by_cases h : ∀ k ∈ g.inputs, k < n
    · rw [fixGate, ite_eq_left ha, ite_eq_left h]
      exact ⟨⟨Or.inl ha,hlen⟩,h,fun _ _ => rfl⟩
    · obtain ⟨k, hbad⟩ := Classical.not_forall.mp h
      have hit : k ∈ g.inputs := by tauto
      have outside : ¬k < n := by tauto
      rw [fixGate, ite_eq_left ha, ite_eq_right h]
      refine ⟨by simp [legal], by simp, ?_⟩
      intro ws hw
      have zero : ws.getD k false = false := List.getD_eq_default _ _ (by omega)
      simp [step,ha,GateOp.eval]
      exact ⟨k,hit,zero⟩
  · change g.op = GateOp.or at ho
    have hne : g.op ≠ .and := by simp [ho]
    rw [fixGate, ite_eq_right hne]
    refine ⟨⟨by simp, (List.length_filter_le ..).trans hlen⟩, ?_, ?_⟩
    · intro k hk
      simpa using (List.mem_filter.mp hk).2
    · intro ws hw
      unfold step
      congr 2
      rw [ho]
      apply Bool.eq_iff_iff.mpr
      simp only [GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true,
        List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨k, ⟨hk,_⟩, val⟩
        exact ⟨k,hk,val⟩
      · rintro ⟨k,hk,val⟩
        refine ⟨k, ⟨hk,?_⟩, val⟩
        by_contra h
        rw [List.getD_eq_default _ _ (by omega)] at val
        contradiction

noncomputable def build (a b : ℕ) : ℕ → List Gate → List Gate
  | _, [] => [⟨.or,[a,b]⟩]
  | n, g::gs => fixGate n g :: build a b (n+1) gs

theorem build_spec (a b n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, legal g)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    (build a b n gs).length = gs.length+1 ∧
    (∀ g ∈ build a b n gs, legal g) ∧
    (∀ j < (build a b n gs).length, ∀ k ∈ ((build a b n gs).getD j ⟨.or,[]⟩).inputs, k < n+j) ∧
    ∀ ws : List Bool, ws.length = n →
      (build a b n gs).foldl step ws =
        let w := gs.foldl step ws
        w ++ [w.getD a false || w.getD b false] := by
  induction gs generalizing n with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at ha hb
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simpa [build,legal]
    · intro j hj k hk
      have : j=0 := by simpa [build] using hj
      subst j
      simp [build] at hk
      rcases hk with rfl | rfl <;> omega
    · intro ws _
      simp [build,step,GateOp.eval]
  | cons g gs ih =>
    have tail := ih (n+1) (fun t ht => hg _ (List.mem_cons_of_mem _ ht))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
    obtain ⟨sz,leg,read,eval⟩ := tail
    obtain ⟨gl,gr,ge⟩ := fix_spec n g (hg g List.mem_cons_self)
    refine ⟨by simp [build,sz], ?_, ?_, ?_⟩
    · simpa [build] using And.intro gl leg
    · intro j hj k hk
      cases j with
      | zero => simpa using gr k (by simpa [build] using hk)
      | succ j =>
        have h := read j (by simpa [build] using hj) k (by simpa [build] using hk)
        omega
    · intro ws hw
      simp only [build, List.foldl_cons, ge ws hw]
      apply eval
      simp [step,hw]

theorem foldLength (gs : List Gate) (ws : List Bool) : (gs.foldl step ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end PEqualNP.Outside.L_meta_18292

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_18292 in
theorem PEqualNP.Outside.L_meta_18292 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin (x1 + x2.size)), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x6 ∧ x6.size = x2.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x7.length = x1 → x6.eval x7 = ((x2.wires x7).getD (↑x4) Bool.false || (x2.wires x7).getD (↑x5) Bool.false) := by
  intro n C mono a b
  obtain ⟨sz,leg,read,he⟩ := build_spec a b n C.gates mono a.isLt b.isLt
  refine ⟨⟨build a b n C.gates,n+C.size⟩, leg, read, sz, ?_⟩
  intro ws hw
  change ((build a b n C.gates).foldl step ws).getD (n+C.size) false = _
  rw [he ws hw]
  have hl : (C.gates.foldl step ws).length = n+C.size := by rw [foldLength,hw]; rfl
  rw [List.getD_append_right _ _ _ _ (by omega),hl,Nat.sub_self]
  rfl
