import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17912
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem extended (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, gs.foldl step w = w ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    exact ⟨_ :: t, by simpa [step, List.append_assoc] using ht, by simp [hl]⟩

theorem keep (w t : List Bool) (j : ℕ) (h : j < w.length) :
    (w ++ t).getD j false = w.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem lastVal (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp

inductive Expr where
  | inp (i : Fin 26)
  | gate (isAnd : Bool) (a b : Expr)

def Expr.cost : Expr → ℕ
  | .inp _ => 0
  | .gate _ a b => a.cost + b.cost + 1

def Expr.val (x : List Bool) : Expr → Bool
  | .inp i => x.getD i.val false
  | .gate op a b => if op then a.val x && b.val x else a.val x || b.val x

def legal (gs : List Gate) := ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem compile (e : Expr) (n : ℕ) (hn : 26 ≤ n) :
    ∃ gs : List Gate, ∃ j : ℕ, legal gs ∧ gs.length = e.cost ∧ j < n + gs.length ∧ (e.cost ≠ 0 → n ≤ j) ∧
    ∀ (x w : List Bool), x.length = 26 → w.length = n →
      (∀ i : Fin 26, w.getD i.val false = x.getD i.val false) →
      (gs.foldl step w).getD j false = e.val x := by
  induction e generalizing n with
  | inp i =>
    exact ⟨[], i.val, by simp [legal], rfl, by simp; omega, by simp [Expr.cost], fun x w _ _ h => h i⟩
  | gate op a b ia ib =>
    obtain ⟨u, i, lu, su, hi, _, hu⟩ := ia n hn
    obtain ⟨v, j, lv, sv, hj, _, hv⟩ := ib (n+u.length) (by omega)
    let g : Gate := ⟨if op then .and else .or, [i,j]⟩
    refine ⟨u ++ v ++ [g], n+u.length+v.length, ?_, ?_, ?_, by omega, ?_⟩
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with (h|h)|rfl
      · exact lu _ h
      · exact lv _ h
      · cases op <;> simp [g]
    · simp [Expr.cost, su, sv, Nat.add_assoc]
    · simp; omega
    · intro x w hx hw base
      obtain ⟨t, et, lt⟩ := extended u w
      obtain ⟨q, eq, lq⟩ := extended v (w ++ t)
      have va := hu x w hx hw base
      rw [et] at va
      have vb := hv x (w++t) hx (by simp [hw,lt]) (fun k => by rw [keep, base]; omega)
      rw [eq] at vb
      have hlen : (w ++ t ++ q).length = n+u.length+v.length := by simp [hw, lt,lq,Nat.add_assoc]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, et, eq]
      unfold step
      rw [← hlen, lastVal]
      have vi : (w++t++q).getD i false = a.val x := by rw [keep,va]; simp; omega
      cases op <;> change _ = _ <;> simp only [g, Bool.false_eq_true, if_false, if_true, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true, vi, vb, Expr.val]

def tree : Expr := (.gate false (.gate true (.inp 4) (.gate false (.inp 18) (.gate false (.inp 22) (.gate false (.inp 23) (.inp 25))))) (.gate false (.gate true (.inp 5) (.gate false (.inp 17) (.gate false (.inp 21) (.gate false (.inp 22) (.inp 24))))) (.gate false (.gate true (.inp 7) (.gate false (.inp 15) (.gate false (.inp 19) (.gate false (.inp 20) (.inp 22))))) (.gate false (.gate true (.inp 8) (.gate false (.inp 14) (.gate false (.inp 18) (.gate false (.inp 19) (.inp 21))))) (.gate false (.gate true (.inp 9) (.gate false (.inp 13) (.gate false (.inp 17) (.gate false (.inp 18) (.inp 20))))) (.gate false (.gate true (.inp 10) (.gate false (.inp 16) (.gate false (.inp 17) (.gate false (.inp 19) (.inp 25))))) (.gate false (.gate true (.inp 11) (.gate false (.inp 15) (.gate false (.inp 16) (.gate false (.inp 18) (.inp 24))))) (.gate true (.inp 12) (.gate false (.inp 14) (.gate false (.inp 15) (.gate false (.inp 17) (.inp 23))))))))))))
def bits (X Y : Finset (Fin 13)) := List.ofFn fun i : Fin 26 => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ X) else decide (Fin.ofNat 13 i.val ∈ Y)

theorem readBit (X Y : Finset (Fin 13)) (i : Fin 26) :
    (bits X Y).getD i.val false = (if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ X) else decide (Fin.ofNat 13 i.val ∈ Y)) := by
  rw [bits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt), Option.getD_some, List.getElem_ofFn]

set_option synthInstance.maxSize 12000 in
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem tree_ok (X Y : Finset (Fin 13)) : tree.val (bits X Y) = decide (∃ a ∈ X, a.val ∉ ([0,1,2,3,6] : List ℕ) ∧ ∃ b ∈ Y, (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) := by
  apply Bool.eq_iff_iff.mpr
  change (((bits X Y).getD 4 false && ((bits X Y).getD 18 false || ((bits X Y).getD 22 false || ((bits X Y).getD 23 false || (bits X Y).getD 25 false)))) || (((bits X Y).getD 5 false && ((bits X Y).getD 17 false || ((bits X Y).getD 21 false || ((bits X Y).getD 22 false || (bits X Y).getD 24 false)))) || (((bits X Y).getD 7 false && ((bits X Y).getD 15 false || ((bits X Y).getD 19 false || ((bits X Y).getD 20 false || (bits X Y).getD 22 false)))) || (((bits X Y).getD 8 false && ((bits X Y).getD 14 false || ((bits X Y).getD 18 false || ((bits X Y).getD 19 false || (bits X Y).getD 21 false)))) || (((bits X Y).getD 9 false && ((bits X Y).getD 13 false || ((bits X Y).getD 17 false || ((bits X Y).getD 18 false || (bits X Y).getD 20 false)))) || (((bits X Y).getD 10 false && ((bits X Y).getD 16 false || ((bits X Y).getD 17 false || ((bits X Y).getD 19 false || (bits X Y).getD 25 false)))) || (((bits X Y).getD 11 false && ((bits X Y).getD 15 false || ((bits X Y).getD 16 false || ((bits X Y).getD 18 false || (bits X Y).getD 24 false)))) || ((bits X Y).getD 12 false && ((bits X Y).getD 14 false || ((bits X Y).getD 15 false || ((bits X Y).getD 17 false || (bits X Y).getD 23 false))))))))))) = true ↔ decide (∃ a ∈ X, a.val ∉ ([0,1,2,3,6] : List ℕ) ∧ ∃ b ∈ Y, (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ)) = true
  have h0 : (bits X Y).getD 0 false = decide ((0 : Fin 13) ∈ X) := readBit X Y 0
  have h1 : (bits X Y).getD 1 false = decide ((1 : Fin 13) ∈ X) := readBit X Y 1
  have h2 : (bits X Y).getD 2 false = decide ((2 : Fin 13) ∈ X) := readBit X Y 2
  have h3 : (bits X Y).getD 3 false = decide ((3 : Fin 13) ∈ X) := readBit X Y 3
  have h4 : (bits X Y).getD 4 false = decide ((4 : Fin 13) ∈ X) := readBit X Y 4
  have h5 : (bits X Y).getD 5 false = decide ((5 : Fin 13) ∈ X) := readBit X Y 5
  have h6 : (bits X Y).getD 6 false = decide ((6 : Fin 13) ∈ X) := readBit X Y 6
  have h7 : (bits X Y).getD 7 false = decide ((7 : Fin 13) ∈ X) := readBit X Y 7
  have h8 : (bits X Y).getD 8 false = decide ((8 : Fin 13) ∈ X) := readBit X Y 8
  have h9 : (bits X Y).getD 9 false = decide ((9 : Fin 13) ∈ X) := readBit X Y 9
  have h10 : (bits X Y).getD 10 false = decide ((10 : Fin 13) ∈ X) := readBit X Y 10
  have h11 : (bits X Y).getD 11 false = decide ((11 : Fin 13) ∈ X) := readBit X Y 11
  have h12 : (bits X Y).getD 12 false = decide ((12 : Fin 13) ∈ X) := readBit X Y 12
  have h13 : (bits X Y).getD 13 false = decide ((0 : Fin 13) ∈ Y) := readBit X Y 13
  have h14 : (bits X Y).getD 14 false = decide ((1 : Fin 13) ∈ Y) := readBit X Y 14
  have h15 : (bits X Y).getD 15 false = decide ((2 : Fin 13) ∈ Y) := readBit X Y 15
  have h16 : (bits X Y).getD 16 false = decide ((3 : Fin 13) ∈ Y) := readBit X Y 16
  have h17 : (bits X Y).getD 17 false = decide ((4 : Fin 13) ∈ Y) := readBit X Y 17
  have h18 : (bits X Y).getD 18 false = decide ((5 : Fin 13) ∈ Y) := readBit X Y 18
  have h19 : (bits X Y).getD 19 false = decide ((6 : Fin 13) ∈ Y) := readBit X Y 19
  have h20 : (bits X Y).getD 20 false = decide ((7 : Fin 13) ∈ Y) := readBit X Y 20
  have h21 : (bits X Y).getD 21 false = decide ((8 : Fin 13) ∈ Y) := readBit X Y 21
  have h22 : (bits X Y).getD 22 false = decide ((9 : Fin 13) ∈ Y) := readBit X Y 22
  have h23 : (bits X Y).getD 23 false = decide ((10 : Fin 13) ∈ Y) := readBit X Y 23
  have h24 : (bits X Y).getD 24 false = decide ((11 : Fin 13) ∈ Y) := readBit X Y 24
  have h25 : (bits X Y).getD 25 false = decide ((12 : Fin 13) ∈ Y) := readBit X Y 25
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩ | ⟨ha, h⟩
    · refine ⟨4, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨5, h, by decide⟩
      · exact ⟨9, h, by decide⟩
      · exact ⟨10, h, by decide⟩
      · exact ⟨12, h, by decide⟩
    · refine ⟨5, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨4, h, by decide⟩
      · exact ⟨8, h, by decide⟩
      · exact ⟨9, h, by decide⟩
      · exact ⟨11, h, by decide⟩
    · refine ⟨7, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨2, h, by decide⟩
      · exact ⟨6, h, by decide⟩
      · exact ⟨7, h, by decide⟩
      · exact ⟨9, h, by decide⟩
    · refine ⟨8, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨1, h, by decide⟩
      · exact ⟨5, h, by decide⟩
      · exact ⟨6, h, by decide⟩
      · exact ⟨8, h, by decide⟩
    · refine ⟨9, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨0, h, by decide⟩
      · exact ⟨4, h, by decide⟩
      · exact ⟨5, h, by decide⟩
      · exact ⟨7, h, by decide⟩
    · refine ⟨10, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨3, h, by decide⟩
      · exact ⟨4, h, by decide⟩
      · exact ⟨6, h, by decide⟩
      · exact ⟨12, h, by decide⟩
    · refine ⟨11, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨2, h, by decide⟩
      · exact ⟨3, h, by decide⟩
      · exact ⟨5, h, by decide⟩
      · exact ⟨11, h, by decide⟩
    · refine ⟨12, ha, by decide, ?_⟩
      rcases h with h | h | h | h
      · exact ⟨1, h, by decide⟩
      · exact ⟨2, h, by decide⟩
      · exact ⟨4, h, by decide⟩
      · exact ⟨10, h, by decide⟩
  · rintro ⟨a, ha, good, b, hb, edge⟩
    have table : ∀ a b : Fin 13, a.val ∉ ([0,1,2,3,6] : List ℕ) → (a.val+b.val)%13 ∈ ([0,1,3,9] : List ℕ) → (a = 4 ∧ b = 5) ∨ (a = 4 ∧ b = 9) ∨ (a = 4 ∧ b = 10) ∨ (a = 4 ∧ b = 12) ∨ (a = 5 ∧ b = 4) ∨ (a = 5 ∧ b = 8) ∨ (a = 5 ∧ b = 9) ∨ (a = 5 ∧ b = 11) ∨ (a = 7 ∧ b = 2) ∨ (a = 7 ∧ b = 6) ∨ (a = 7 ∧ b = 7) ∨ (a = 7 ∧ b = 9) ∨ (a = 8 ∧ b = 1) ∨ (a = 8 ∧ b = 5) ∨ (a = 8 ∧ b = 6) ∨ (a = 8 ∧ b = 8) ∨ (a = 9 ∧ b = 0) ∨ (a = 9 ∧ b = 4) ∨ (a = 9 ∧ b = 5) ∨ (a = 9 ∧ b = 7) ∨ (a = 10 ∧ b = 3) ∨ (a = 10 ∧ b = 4) ∨ (a = 10 ∧ b = 6) ∨ (a = 10 ∧ b = 12) ∨ (a = 11 ∧ b = 2) ∨ (a = 11 ∧ b = 3) ∨ (a = 11 ∧ b = 5) ∨ (a = 11 ∧ b = 11) ∨ (a = 12 ∧ b = 1) ∨ (a = 12 ∧ b = 2) ∨ (a = 12 ∧ b = 4) ∨ (a = 12 ∧ b = 10) := by decide +kernel
    rcases table a b good edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (Or.inl ⟨ha, (Or.inl hb)⟩)
    · exact (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩)
    · exact (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩)
    · exact (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩)
    · exact (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩))
    · exact (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩))
    · exact (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩))
    · exact (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩))
    · exact (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩)))
    · exact (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩)))
    · exact (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩)))
    · exact (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩)))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩)))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inl hb)⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inl hb))⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, (Or.inl hb)⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, (Or.inr (Or.inl hb))⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, (Or.inr (Or.inr (Or.inl hb)))⟩)))))))
    · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, (Or.inr (Or.inr (Or.inr hb)))⟩)))))))
end PEqualNP.Outside.L_meta_17912
open PEqualNP.Outside.L_meta_17912 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_17912 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => List.ofFn fun (x4 : Fin (26 : ℕ)) => if ↑x4 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x2) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x4 ∈ x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (23 : ℕ) → x3.output < (26 : ℕ) + x3.size → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 ∧ x7.size ≤ (62 : ℕ) ∧ x3.output < x8 ∧ ∀ (x9 x10 : Finset (Fin (13 : ℕ))), (x7.wires (x2 x9 x10)).getD x3.output Bool.false = x3.eval (x2 x9 x10) ∧ (x7.wires (x2 x9 x10)).getD x8 Bool.false = Decidable.decide (∃ x11 ∈ x9, ↑x11 ∉ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (3 : ℕ), (6 : ℕ)] ∧ ∃ x12 ∈ x10, x1 x11 x12) := by
  dsimp only
  intro C hm small bound
  obtain ⟨gs,j,hg,sz,hj,freshness,ev⟩ := compile tree (26+C.size) (by omega)
  let D : Circuit := ⟨C.gates ++ gs, j⟩
  have cost : gs.length = 39 := sz
  have fresh : 26 + C.size ≤ j := freshness (by decide)
  refine ⟨D,j,?_,?_,by omega,?_⟩
  · intro g h
    rcases List.mem_append.mp h with h|h
    · exact hm g h
    · obtain ⟨op,l⟩ := hg g h
      exact ⟨by simpa using op,l⟩
  · change (C.gates ++ gs).length ≤ 62
    simp only [List.length_append]; change C.size + gs.length ≤ 62; omega
  · intro X Y
    let x := bits X Y
    obtain ⟨t,et,lt⟩ := extended C.gates x
    change ((C.gates ++ gs).foldl step x).getD C.output false = _ ∧ ((C.gates ++ gs).foldl step x).getD j false = _
    rw [List.foldl_append, et]
    have len : x.length = 26 := List.length_ofFn
    have lw : (x++t).length = 26+C.size := by simp [len,lt,Circuit.size]
    obtain ⟨q,eq,_⟩ := extended gs (x++t)
    constructor
    · change _ = (C.gates.foldl step x).getD C.output false
      rw [et,eq,keep _ _ _ (by omega)]
    · exact (ev x (x++t) len lw (fun i => keep _ _ _ (by omega))).trans (tree_ok X Y)
