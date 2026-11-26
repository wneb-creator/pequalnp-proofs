import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17766_aux.Geometry

abbrev V := Fin 26

def rel (u v : V) : Prop := u.val < 13 ∧ 13 ≤ v.val ∧
  (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List Nat)
instance (u v : V) : Decidable (rel u v) := by unfold rel; infer_instance
def edge (u v : V) : Prop := rel u v ∨ rel v u
instance (u v : V) : Decidable (edge u v) := by unfold edge; infer_instance

def Good (f : V → V) : Prop :=
  (∀ u v, edge (f u) (f v) ↔ edge u v) ∧
  ((f 0 = 0 ∧ f 13 = 13) ∨ (f 0 = 13 ∧ f 13 = 0))

def gen (b : Bool) (v : V) : V := ((if b then #[0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25] else #[13, 17, 14, 23, 21, 22, 15, 19, 18, 25, 16, 20, 24, 0, 4, 10, 11, 9, 5, 2, 6, 8, 12, 3, 7, 1]) : Array V)[v.val]?.getD 0
def inv (b : Bool) (v : V) : V := ((if b then #[0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25] else #[13, 25, 19, 23, 14, 18, 20, 24, 21, 17, 15, 16, 22, 0, 2, 6, 10, 1, 8, 7, 11, 4, 5, 3, 12, 9]) : Array V)[v.val]?.getD 0

theorem inverse_tables : ∀ (b : Bool) (v : V), inv b (gen b v) = v ∧ gen b (inv b v) = v := by decide +kernel
def perm (b : Bool) : V ≃ V := ⟨gen b,inv b,fun v => (inverse_tables b v).1,fun v => (inverse_tables b v).2⟩
theorem generator_good : ∀ b, Good (gen b) := by unfold Good; decide +kernel

theorem Good.comp {f g : V → V} (hf : Good f) (hg : Good g) : Good (f ∘ g) := by
  refine ⟨fun a b => (hf.1 _ _).trans (hg.1 a b),?_⟩
  rcases hf.2 with H | H <;> rcases hg.2 with K | K <;> simp [Function.comp_def,H.1,H.2,K.1,K.2]

def move : Nat → Nat → V ≃ V
  | 0,_ => Equiv.refl _
  | n+1, k => if k ≤ 1 then Equiv.refl _ else (perm (k%2==1)).trans (move n (k/2))

theorem move_good : ∀ n k, Good (move n k) := by
  have refl : Good id := ⟨fun _ _ => Iff.rfl,Or.inl ⟨rfl,rfl⟩⟩
  intro n
  induction n with
  | zero => intro k; exact refl
  | succ n ih =>
    intro k
    simp only [move]
    split
    · exact refl
    · exact (ih _).comp (generator_good _)

def reps : List (V × V) := [(0,1), (0,2), (0,13), (0,14), (0,17), (1,2), (1,3), (1,14), (1,15), (1,17), (2,4), (2,8), (2,14), (2,16)]
private def codes0 : Array Nat := #[1, 1, 1, 34, 136, 64, 9, 4, 34, 4, 74, 36, 16, 1, 1, 276, 69, 1, 33, 4, 34, 132, 64, 3, 16, 4]

private theorem row0 : ∀ b : V, (0:V) ≠ b →
    let u := move 8 (codes0[b.val]?.getD 1)
    (min (u 0) (u b),max (u 0) (u b)) ∈ reps := by decide +kernel

private def codes1 : Array Nat := #[1, 1, 1, 1, 554, 73, 576, 1153, 33, 10, 516, 36, 16, 2, 1, 1, 16, 1, 33, 520, 33, 84, 40, 3, 16, 2]

private theorem row1 : ∀ b : V, (1:V) ≠ b →
    let u := move 10 (codes1[b.val]?.getD 1)
    (min (u 1) (u b),max (u 1) (u b)) ∈ reps := by decide +kernel

private def codes2 : Array Nat := #[1, 1, 1, 544, 1, 544, 9, 4, 1, 2216, 3, 596, 3, 2, 1, 544, 1, 260, 41, 2, 3, 196, 394, 148, 20, 2]

private theorem row2 : ∀ b : V, (2:V) ≠ b →
    let u := move 11 (codes2[b.val]?.getD 1)
    (min (u 2) (u b),max (u 2) (u b)) ∈ reps := by decide +kernel

private def codes3 : Array Nat := #[34, 1, 544, 1, 136, 276, 296, 593, 34, 4, 74, 553, 69, 6, 74, 276, 69, 24, 34, 296, 34, 82, 170, 49, 69, 6]

private theorem row3 : ∀ b : V, (3:V) ≠ b →
    let u := move 9 (codes3[b.val]?.getD 1)
    (min (u 3) (u b),max (u 3) (u b)) ∈ reps := by decide +kernel

private def codes4 : Array Nat := #[136, 554, 1, 136, 1, 192, 149, 4, 130, 132, 516, 132, 136, 264, 264, 132, 136, 264, 49, 5, 388, 132, 208, 37, 328, 65]

private theorem row4 : ∀ b : V, (4:V) ≠ b →
    let u := move 9 (codes4[b.val]?.getD 1)
    (min (u 4) (u b),max (u 4) (u b)) ∈ reps := by decide +kernel

private def codes5 : Array Nat := #[64, 73, 544, 276, 192, 1, 73, 12, 97, 64, 192, 276, 64, 128, 416, 288, 64, 128, 73, 13, 192, 65, 64, 17, 160, 80]

private theorem row5 : ∀ b : V, (5:V) ≠ b →
    let u := move 9 (codes5[b.val]?.getD 1)
    (min (u 5) (u b),max (u 5) (u b)) ∈ reps := by decide +kernel

private def codes6 : Array Nat := #[9, 576, 9, 296, 149, 73, 1, 12, 33, 9, 9, 25, 69, 17, 21, 9, 37, 128, 17, 9, 18, 194, 96, 17, 8, 2]

private theorem row6 : ∀ b : V, (6:V) ≠ b →
    let u := move 9 (codes6[b.val]?.getD 1)
    (min (u 6) (u b),max (u 6) (u b)) ∈ reps := by decide +kernel

private def codes7 : Array Nat := #[4, 1153, 4, 593, 4, 12, 12, 1, 34, 4, 74, 36, 16, 8, 10, 4, 12, 8, 26, 4, 18, 164, 80, 257, 8, 5]

private theorem row7 : ∀ b : V, (7:V) ≠ b →
    let u := move 10 (codes7[b.val]?.getD 1)
    (min (u 7) (u b),max (u 7) (u b)) ∈ reps := by decide +kernel

private def codes8 : Array Nat := #[34, 33, 1, 34, 130, 97, 33, 34, 1, 292, 98, 129, 48, 66, 98, 97, 33, 42, 33, 82, 34, 66, 210, 41, 52, 66]

private theorem row8 : ∀ b : V, (8:V) ≠ b →
    let u := move 8 (codes8[b.val]?.getD 1)
    (min (u 8) (u b),max (u 8) (u b)) ∈ reps := by decide +kernel

private def codes9 : Array Nat := #[4, 10, 2216, 4, 132, 64, 9, 4, 292, 1, 144, 129, 586, 8, 130, 64, 9, 8, 21, 4, 4, 132, 64, 12, 10, 4]

private theorem row9 : ∀ b : V, (9:V) ≠ b →
    let u := move 11 (codes9[b.val]?.getD 1)
    (min (u 9) (u b),max (u 9) (u b)) ∈ reps := by decide +kernel

private def codes10 : Array Nat := #[74, 516, 3, 74, 516, 192, 9, 74, 98, 144, 1, 100, 144, 138, 272, 288, 144, 18, 128, 2, 74, 66, 144, 138, 24, 32]

private theorem row10 : ∀ b : V, (10:V) ≠ b →
    let u := move 9 (codes10[b.val]?.getD 1)
    (min (u 10) (u b),max (u 10) (u b)) ∈ reps := by decide +kernel

private def codes11 : Array Nat := #[36, 36, 596, 553, 132, 276, 25, 36, 129, 129, 100, 1, 48, 68, 776, 148, 72, 8, 384, 6, 36, 68, 32, 68, 36, 66]

private theorem row11 : ∀ b : V, (11:V) ≠ b →
    let u := move 9 (codes11[b.val]?.getD 1)
    (min (u 11) (u b),max (u 11) (u b)) ∈ reps := by decide +kernel

private def codes12 : Array Nat := #[16, 16, 3, 69, 136, 64, 69, 16, 48, 586, 144, 48, 1, 32, 197, 48, 72, 20, 105, 40, 16, 104, 32, 85, 16, 32]

private theorem row12 : ∀ b : V, (12:V) ≠ b →
    let u := move 9 (codes12[b.val]?.getD 1)
    (min (u 12) (u b),max (u 12) (u b)) ∈ reps := by decide +kernel

private def codes13 : Array Nat := #[1, 2, 2, 6, 264, 128, 17, 8, 66, 8, 138, 68, 32, 1, 272, 148, 37, 8, 17, 2, 18, 68, 32, 17, 8, 2]

private theorem row13 : ∀ b : V, (13:V) ≠ b →
    let u := move 8 (codes13[b.val]?.getD 1)
    (min (u 13) (u b),max (u 13) (u b)) ∈ reps := by decide +kernel

private def codes14 : Array Nat := #[1, 1, 1, 74, 264, 416, 21, 10, 98, 130, 272, 776, 197, 272, 1, 1032, 264, 264, 17, 2, 298, 260, 272, 272, 8, 1108]

private theorem row14 : ∀ b : V, (14:V) ≠ b →
    let u := move 10 (codes14[b.val]?.getD 1)
    (min (u 14) (u b),max (u 14) (u b)) ∈ reps := by decide +kernel

private def codes15 : Array Nat := #[276, 1, 544, 276, 132, 288, 9, 4, 97, 64, 288, 148, 48, 148, 1032, 1, 37, 288, 384, 6, 18, 196, 288, 148, 148, 1032]

private theorem row15 : ∀ b : V, (15:V) ≠ b →
    let u := move 10 (codes15[b.val]?.getD 1)
    (min (u 15) (u b),max (u 15) (u b)) ∈ reps := by decide +kernel

private def codes16 : Array Nat := #[69, 16, 1, 69, 136, 64, 37, 12, 33, 9, 144, 72, 72, 37, 264, 37, 1, 258, 49, 37, 50, 258, 96, 37, 72, 72]

private theorem row16 : ∀ b : V, (16:V) ≠ b →
    let u := move 8 (codes16[b.val]?.getD 1)
    (min (u 16) (u b),max (u 16) (u b)) ∈ reps := by decide +kernel

private def codes17 : Array Nat := #[1, 1, 260, 24, 264, 128, 128, 8, 42, 8, 18, 8, 20, 8, 264, 288, 258, 1, 128, 2177, 18, 277, 137, 8, 8, 5]

private theorem row17 : ∀ b : V, (17:V) ≠ b →
    let u := move 11 (codes17[b.val]?.getD 1)
    (min (u 17) (u b),max (u 17) (u b)) ∈ reps := by decide +kernel

private def codes18 : Array Nat := #[33, 33, 41, 34, 49, 73, 17, 26, 33, 21, 128, 384, 105, 17, 17, 384, 49, 128, 1, 17, 146, 65, 128, 17, 24, 146]

private theorem row18 : ∀ b : V, (18:V) ≠ b →
    let u := move 8 (codes18[b.val]?.getD 1)
    (min (u 18) (u b),max (u 18) (u b)) ∈ reps := by decide +kernel

private def codes19 : Array Nat := #[4, 520, 2, 296, 5, 13, 9, 4, 82, 4, 2, 6, 40, 2, 2, 6, 37, 2177, 17, 1, 18, 2, 6, 1088, 8, 2]

private theorem row19 : ∀ b : V, (19:V) ≠ b →
    let u := move 11 (codes19[b.val]?.getD 1)
    (min (u 19) (u b),max (u 19) (u b)) ∈ reps := by decide +kernel

private def codes20 : Array Nat := #[34, 33, 3, 34, 388, 192, 18, 18, 34, 4, 74, 36, 16, 18, 298, 18, 50, 18, 146, 18, 1, 66, 138, 592, 24, 145]

private theorem row20 : ∀ b : V, (20:V) ≠ b →
    let u := move 9 (codes20[b.val]?.getD 1)
    (min (u 20) (u b),max (u 20) (u b)) ∈ reps := by decide +kernel

private def codes21 : Array Nat := #[132, 84, 196, 82, 132, 65, 194, 164, 66, 132, 66, 68, 104, 68, 260, 196, 258, 277, 65, 2, 66, 1, 96, 68, 68, 66]

private theorem row21 : ∀ b : V, (21:V) ≠ b →
    let u := move 8 (codes21[b.val]?.getD 1)
    (min (u 21) (u b),max (u 21) (u b)) ∈ reps := by decide +kernel

private def codes22 : Array Nat := #[64, 40, 394, 170, 208, 64, 96, 80, 210, 64, 144, 32, 32, 32, 272, 288, 96, 137, 128, 6, 138, 96, 1, 138, 32, 32]

private theorem row22 : ∀ b : V, (22:V) ≠ b →
    let u := move 8 (codes22[b.val]?.getD 1)
    (min (u 22) (u b),max (u 22) (u b)) ∈ reps := by decide +kernel

private def codes23 : Array Nat := #[3, 3, 148, 49, 37, 17, 17, 257, 41, 12, 138, 68, 85, 17, 272, 148, 37, 8, 17, 1088, 592, 68, 138, 1, 257, 2]

private theorem row23 : ∀ b : V, (23:V) ≠ b →
    let u := move 10 (codes23[b.val]?.getD 1)
    (min (u 23) (u b),max (u 23) (u b)) ∈ reps := by decide +kernel

private def codes24 : Array Nat := #[16, 16, 20, 69, 328, 160, 8, 8, 52, 10, 24, 36, 16, 8, 8, 148, 72, 8, 24, 8, 24, 68, 32, 257, 1, 293]

private theorem row24 : ∀ b : V, (24:V) ≠ b →
    let u := move 8 (codes24[b.val]?.getD 1)
    (min (u 24) (u b),max (u 24) (u b)) ∈ reps := by decide +kernel

private def codes25 : Array Nat := #[4, 2, 2, 6, 65, 80, 2, 5, 66, 4, 32, 66, 32, 2, 1108, 1032, 72, 5, 146, 2, 145, 66, 32, 2, 293, 1]

private theorem row25 : ∀ b : V, (25:V) ≠ b →
    let u := move 10 (codes25[b.val]?.getD 1)
    (min (u 25) (u b),max (u 25) (u b)) ∈ reps := by decide +kernel

theorem representatives (a b : V) (ne : a ≠ b) :
    ∃ s : V ≃ V, Good s ∧ (min (s a) (s b),max (s a) (s b)) ∈ reps := by
  fin_cases a
  · exact ⟨move 8 (codes0[b.val]?.getD 1),move_good _ _, row0 b ne⟩
  · exact ⟨move 10 (codes1[b.val]?.getD 1),move_good _ _, row1 b ne⟩
  · exact ⟨move 11 (codes2[b.val]?.getD 1),move_good _ _, row2 b ne⟩
  · exact ⟨move 9 (codes3[b.val]?.getD 1),move_good _ _, row3 b ne⟩
  · exact ⟨move 9 (codes4[b.val]?.getD 1),move_good _ _, row4 b ne⟩
  · exact ⟨move 9 (codes5[b.val]?.getD 1),move_good _ _, row5 b ne⟩
  · exact ⟨move 9 (codes6[b.val]?.getD 1),move_good _ _, row6 b ne⟩
  · exact ⟨move 10 (codes7[b.val]?.getD 1),move_good _ _, row7 b ne⟩
  · exact ⟨move 8 (codes8[b.val]?.getD 1),move_good _ _, row8 b ne⟩
  · exact ⟨move 11 (codes9[b.val]?.getD 1),move_good _ _, row9 b ne⟩
  · exact ⟨move 9 (codes10[b.val]?.getD 1),move_good _ _, row10 b ne⟩
  · exact ⟨move 9 (codes11[b.val]?.getD 1),move_good _ _, row11 b ne⟩
  · exact ⟨move 9 (codes12[b.val]?.getD 1),move_good _ _, row12 b ne⟩
  · exact ⟨move 8 (codes13[b.val]?.getD 1),move_good _ _, row13 b ne⟩
  · exact ⟨move 10 (codes14[b.val]?.getD 1),move_good _ _, row14 b ne⟩
  · exact ⟨move 10 (codes15[b.val]?.getD 1),move_good _ _, row15 b ne⟩
  · exact ⟨move 8 (codes16[b.val]?.getD 1),move_good _ _, row16 b ne⟩
  · exact ⟨move 11 (codes17[b.val]?.getD 1),move_good _ _, row17 b ne⟩
  · exact ⟨move 8 (codes18[b.val]?.getD 1),move_good _ _, row18 b ne⟩
  · exact ⟨move 11 (codes19[b.val]?.getD 1),move_good _ _, row19 b ne⟩
  · exact ⟨move 9 (codes20[b.val]?.getD 1),move_good _ _, row20 b ne⟩
  · exact ⟨move 8 (codes21[b.val]?.getD 1),move_good _ _, row21 b ne⟩
  · exact ⟨move 8 (codes22[b.val]?.getD 1),move_good _ _, row22 b ne⟩
  · exact ⟨move 10 (codes23[b.val]?.getD 1),move_good _ _, row23 b ne⟩
  · exact ⟨move 8 (codes24[b.val]?.getD 1),move_good _ _, row24 b ne⟩
  · exact ⟨move 10 (codes25[b.val]?.getD 1),move_good _ _, row25 b ne⟩

abbrev point (p : Fin 13) : V := Fin.castAdd 13 p
abbrev line (l : Fin 13) : V := Fin.natAdd 13 l

theorem primitive : ∀ p l : Fin 13, rel (point p) (line l) ↔
    (p-l) ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide +kernel
theorem point_recover : ∀ u : V, u.val<13 → u=point (Fin.ofNat 13 u.val) := by decide +kernel
theorem line_recover : ∀ u : V, 13≤u.val → u=line (Fin.ofNat 13 u.val) := by decide +kernel

theorem geometry : ∀ u v : V, edge u v ↔ ∃ p l : Fin 13,
    (p-l) ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
    ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) := by
  intro u v
  have sides (x y : V) (h : rel x y) : ∃ p l : Fin 13,
      (p-l) ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x=point p ∧ y=line l := by
    have hx := point_recover x h.1
    have hy := line_recover y h.2.1
    exact ⟨_,_,(primitive _ _).mp (by rw [←hx,←hy]; exact h),hx,hy⟩
  constructor
  · rintro (forward | backward)
    · obtain ⟨p,l,i,hp,hl⟩ := sides _ _ forward
      exact ⟨p,l,i,Or.inl ⟨hp,hl⟩⟩
    · obtain ⟨p,l,i,hp,hl⟩ := sides _ _ backward
      exact ⟨p,l,i,Or.inr ⟨hp,hl⟩⟩
  · rintro ⟨p,l,i,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ((primitive _ _).mpr i)
    · exact Or.inr ((primitive _ _).mpr i)

end PEqualNP.Outside.L_meta_17766_aux.Geometry
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo

namespace PEqualNP.Outside.L_meta_17766_aux.Transport

abbrev V := Fin 26
def rho (s : V → V) (i : Nat) := if h : i<26 then (s ⟨i,h⟩).val else i
def gate (s : V → V) (g : Gate) : Gate := ⟨g.op,g.inputs.map (rho s)⟩
def rename (s : V → V) (C : Circuit) : Circuit := ⟨C.gates.map (gate s),rho s C.output⟩

theorem rho_raw (s : V → V) (v : V) : rho s v.val = (s v).val := by simp [rho]
theorem rho_internal (s : V → V) {i : Nat} (h : 26 ≤ i) : rho s i = i := by simp [rho,show ¬i<26 by omega]

def traceStep {α : Type} (node : GateOp → List α → α) (d : α) (w : List α) (g : Gate) :=
  w ++ [node g.op (g.inputs.map fun i => w.getD i d)]

theorem trace_relabel {α : Type} (node : GateOp → List α → α) (d : α) (s : V → V)
    (C : Circuit) (x : V → α) (a : Nat) :
    ((rename s C).gates.foldl (traceStep node d) (List.ofFn x)).getD (rho s a) d =
      (C.gates.foldl (traceStep node d) (List.ofFn (x ∘ s))).getD a d := by
  have same (T : List α) (i : Nat) :
      (List.ofFn x ++ T).getD (rho s i) d = (List.ofFn (x ∘ s) ++ T).getD i d := by
    by_cases hi : i < 26
    · have hi' : rho s i < 26 := by simpa only [rho,dif_pos hi] using (s ⟨i,hi⟩).isLt
      rw [List.getD_append _ _ _ _ (by simpa using hi'),List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hi'),List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn,List.getElem_ofFn]
      congr 1
      apply Fin.ext
      exact dif_pos hi
    · rw [rho_internal _ (by omega),List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,List.length_ofFn]
  have fold (gs : List Gate) (T : List α) : ∃ U : List α,
      (gs.map (gate s)).foldl (traceStep node d) (List.ofFn x ++ T) = List.ofFn x ++ U ∧
      gs.foldl (traceStep node d) (List.ofFn (x ∘ s) ++ T) = List.ofFn (x ∘ s) ++ U := by
    induction gs generalizing T with
    | nil => exact ⟨T,rfl,rfl⟩
    | cons g gs ih =>
      have val : ((g.inputs.map (rho s)).map (fun i => (List.ofFn x ++ T).getD i d)) =
          g.inputs.map (fun i => (List.ofFn (x ∘ s) ++ T).getD i d) := by
        rw [List.map_map];exact List.map_congr_left fun i _ => same T i
      obtain ⟨U,h₁,h₂⟩ := ih (T ++ [node g.op (g.inputs.map (fun i => (List.ofFn (x ∘ s) ++ T).getD i d))])
      exact ⟨U,by simpa only [List.map_cons,List.foldl_cons,traceStep,gate,val,List.append_assoc] using h₁,
        by simpa only [List.foldl_cons,traceStep,List.append_assoc] using h₂⟩
  obtain ⟨U,h₁,h₂⟩ := fold C.gates []
  simp only [List.append_nil] at h₁ h₂
  change ((C.gates.map (gate s)).foldl (traceStep node d) (List.ofFn x)).getD (rho s a) d = _
  rw [h₁,h₂]
  exact same U a

theorem wires (s : V → V) (C : Circuit) (x : V → Bool) (a : Nat) :
    wval (rename s C) x (rho s a) = wval C (x ∘ s) a :=
  trace_relabel GateOp.eval false s C x a

def sc (op : GateOp) (l : List (Option Nat)) : Option Nat :=
  match op with
  | .or => l.foldl (fun acc o => match acc,o with
      | none,o => o | some a,none => some a | some a,some b => some (min a b)) none
  | .and => l.foldl (fun acc o => match acc,o with
      | some a,some b => some (a+b) | _,_ => none) (some 0)
  | _ => none

def seed (v i : Nat) : Option Nat :=
  if i=v then some 1 else if i ∈ ([0,13] : List Nat) then some 0 else none

theorem seed_list (v : Nat) : (List.range 26).map (seed v) = List.ofFn (fun j : V => seed v j.val) := by
  apply List.ext_getElem
  · simp
  · intro i h h';simp only [List.getElem_map,List.getElem_ofFn,List.getElem_range]

theorem seed_perm (s : V ≃ V) (h : PEqualNP.Outside.L_meta_17766_aux.Geometry.Good s) (i v : V) :
    seed (s v).val (s i).val = seed v.val i.val := by
  have same : (s i).val = (s v).val ↔ i.val=v.val := by rw [Fin.val_inj,Fin.val_inj, s.injective.eq_iff]
  have mem : (s i).val ∈ ([0,13] : List Nat) ↔ i.val ∈ ([0,13] : List Nat) := by
    change (s i).val ∈ [0,13] ↔ i.val ∈ [0,13]
    have zero (j : V) : j.val=0 ↔ j=0 := by change j.val=(0:V).val ↔ _;exact Fin.val_inj
    have thirt (j : V) : j.val=13 ↔ j=13 := by change j.val=(13:V).val ↔ _;exact Fin.val_inj
    simp only [List.mem_cons,List.not_mem_nil,or_false,zero,thirt]
    rcases h.2 with H | H <;> constructor
    · rintro (h0 | h13)
      · exact Or.inl (s.injective (h0.trans H.1.symm))
      · exact Or.inr (s.injective (h13.trans H.2.symm))
    · rintro (rfl | rfl) <;> simp [H.1,H.2]
    · rintro (h0 | h13)
      · exact Or.inr (s.injective (h0.trans H.2.symm))
      · exact Or.inl (s.injective (h13.trans H.1.symm))
    · rintro (rfl | rfl) <;> simp [H.1,H.2]
  simp only [seed,same,mem]

theorem scalar (s : V ≃ V) (good : PEqualNP.Outside.L_meta_17766_aux.Geometry.Good s) (C : Circuit) (v : V) (w : Nat) :
    (scalarMults (rename s C) 26 [0,13] (s v).val).getD (rho s w) none =
    (scalarMults C 26 [0,13] v.val).getD w none := by
  change ((rename s C).gates.foldl (traceStep sc none) ((List.range 26).map (seed (s v).val))).getD _ _ =
    (C.gates.foldl (traceStep sc none) ((List.range 26).map (seed v.val))).getD _ _
  rw [seed_list,seed_list,trace_relabel]
  congr 3
  funext i
  exact seed_perm s good i v

end PEqualNP.Outside.L_meta_17766_aux.Transport
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_17766_aux.Geometry PEqualNP.Outside.L_meta_17766_aux.Transport

namespace PEqualNP.Outside.L_meta_17766_aux.Canonical

abbrev F := fpl 13 (fun (p l : Fin 13) => p-l ∈ ({0,1,3,9} : Finset (Fin 13)))
abbrev OK (C : Circuit) := IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
  (∀ x : Fin 26 → Bool, (∀ i, x i = F x → F (Function.update x i (!x i)) ≠ F x) → circuitFun 26 C x = F x) ∧
  0 < andPairs 26 C ∧ ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
     ∃ y : Fin 26 → Bool, wval C y (26+j) = true ∧ circuitFun 26 C y = false
abbrev Win (C : Circuit) := ∃ v ∈ ([0,13] : List ℕ), (scalarMults C 26 [0,13] v).getD C.output none = some 1

theorem edge_fun (x : Fin 26 → Bool) :
    F x = true ↔ ∃ a b, edge a b ∧ x a = true ∧ x b = true := by
  unfold F fpl
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨p,l,adj,xp,xl⟩
    exact ⟨_,_,(geometry _ _).mpr ⟨p,l,adj,Or.inl ⟨rfl,rfl⟩⟩,xp,xl⟩
  · rintro ⟨a,b,adj,xa,xb⟩
    obtain ⟨p,l,hi,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (geometry _ _).mp adj
    · exact ⟨p,l,hi,xa,xb⟩
    · exact ⟨p,l,hi,xb,xa⟩

theorem fperm (s : Equiv.Perm (Fin 26)) (hs : Good s) (x : Fin 26 → Bool) :
    F (x ∘ s) = F x := by
  apply Bool.eq_iff_iff.mpr
  rw [edge_fun,edge_fun]
  constructor
  · rintro ⟨a,b,h,xa,xb⟩
    exact ⟨s a,s b,(hs.1 _ _).mpr h,xa,xb⟩
  · rintro ⟨a,b,h,xa,xb⟩
    exact ⟨s.symm a,s.symm b,(hs.1 _ _).mp (by simpa using h),by simpa using xa,by simpa using xb⟩

theorem updated (s : Equiv.Perm (Fin 26)) (x : Fin 26 → Bool) (i : Fin 26) :
    (Function.update x (s i) (!(x (s i)))) ∘ s = Function.update (x ∘ s) i (!x (s i)) := by
  funext j
  by_cases h : j=i
  · subst j; simp
  · simp [Function.update_of_ne (s.injective.ne h),Function.update_of_ne h]

theorem eval_renamed (s : Equiv.Perm (Fin 26)) (C : Circuit) (x : Fin 26 → Bool) :
    circuitFun 26 (rename s C) x = circuitFun 26 C (x ∘ s) := wires s C x C.output

theorem boundary (s : Equiv.Perm (Fin 26)) (hs : Good s) (C : Circuit)
    (correct : ∀ x : Fin 26 → Bool, (∀ i, x i = F x → F (Function.update x i (!x i)) ≠ F x) → circuitFun 26 C x = F x) :
    ∀ x : Fin 26 → Bool, (∀ i, x i = F x → F (Function.update x i (!x i)) ≠ F x) →
       circuitFun 26 (rename s C) x = F x := by
  intro x hx
  rw [eval_renamed,←fperm s hs x]
  apply correct
  intro i hi
  rw [fperm s hs] at hi ⊢
  have nx := hx (s i) hi
  rw [←fperm s hs (Function.update x (s i) (!(x (s i)))),updated] at nx
  exact nx

theorem gate_at (s : Fin 26 → Fin 26) (C : Circuit) (i : Nat) :
    gateAt (rename s C) i = gate s (gateAt C i) := by
  unfold gateAt rename
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases C.gates[i]? <;> rfl

theorem rho_inj (s : Equiv.Perm (Fin 26)) : Function.Injective (rho s) := by
  have back (i : Nat) : rho s.symm (rho s i)=i := by
    by_cases h : i<26
    · change rho s.symm (if h : i < 26 then (s ⟨i,h⟩).val else i) = i
      rw [dif_pos h,rho_raw,s.symm_apply_apply]
    · have ge : 26 ≤ i := by omega
      rw [rho_internal s ge,rho_internal s.symm ge]
  exact Function.LeftInverse.injective back

theorem preserve_model (s : Equiv.Perm (Fin 26)) (C : Circuit) (ao : IsAO2 26 C)
    (nodup : ∀ g ∈ C.gates, g.inputs.Nodup) :
    IsAO2 26 (rename s C) ∧ ∀ g ∈ (rename s C).gates, g.inputs.Nodup := by
  have raw (i j : Nat) (h : i<26+j) : rho s i<26+j := by
    by_cases hi : i<26
    · have : rho s i < 26 := by simpa only [rho,dif_pos hi] using (s ⟨i,hi⟩).isLt
      omega
    · rw [rho_internal _ (by omega)];exact h
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro g hg; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg; exact ao.1 q hq
  · intro j hj i hi
    rw [gate_at] at hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    exact raw _ _ (ao.2.1 j (by simpa [rename] using hj) k hk)
  · intro g hg; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simpa [gate] using ao.2.2 q hq
  · intro g hg; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact (nodup q hq).map (rho_inj s)

theorem relabel_cones : ∀ (π : Fin 26 → Fin 26) (D : Circuit),
    let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
    let D' : Circuit := ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), ρ D.output⟩
    cones 26 D' = cones 26 D := by
  intro π D
  let ρ : ℕ → ℕ := fun i => if h : i < 26 then (π ⟨i, h⟩).val else i
  have hρ_lt : ∀ i, i < 26 → ρ i < 26 := by
    intro i hi; dsimp only [ρ]; rw [dif_pos hi]; exact (π ⟨i, hi⟩).isLt
  have hρ_ge : ∀ i, 26 ≤ i → ρ i = i := by
    intro i hi; dsimp only [ρ]; rw [dif_neg (by omega)]
  have hfold : ∀ (gs : List Gate) (cs : List (List ℕ)),
      (gs.map (fun g => Gate.mk g.op (g.inputs.map ρ))).foldl (coneStep 26) cs =
        gs.foldl (coneStep 26) cs := by
    intro gs
    induction gs with
    | nil => intro cs; rfl
    | cons g rest ih =>
      intro cs
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hstep : coneStep 26 cs ⟨g.op, g.inputs.map ρ⟩ = coneStep 26 cs g := by
        change cs ++ [(((g.inputs.map ρ).filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
          (fun w => (w - 26) :: cs.getD (w - 26) []))] =
          cs ++ [((g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
            (fun w => (w - 26) :: cs.getD (w - 26) []))]
        congr 2
        rw [List.filter_map, List.flatMap_map]
        have hcomp : ∀ (l : List ℕ) (f1 f2 : ℕ → List ℕ),
            (∀ w ∈ l, f1 w = f2 w) → l.flatMap f1 = l.flatMap f2 := by
          intro l f1 f2 h; induction l with
          | nil => rfl
          | cons x xs ihxs => simp [h x (by simp), ihxs (fun w hw => h w (by simp [hw]))]
        have hflt_eq : g.inputs.filter ((fun w => decide (26 ≤ w ∧ w < 26 + cs.length)) ∘ ρ) =
            g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length)) := by
          apply List.filter_congr
          intro x _
          simp only [Function.comp_apply]
          by_cases hx : x < 26
          · have := hρ_lt x hx
            simp [show ¬ (26 ≤ ρ x ∧ ρ x < 26 + cs.length) by omega,
                  show ¬ (26 ≤ x ∧ x < 26 + cs.length) by omega]
          · simp [hρ_ge x (by omega)]
        rw [hflt_eq]
        apply hcomp
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        simp [hρ_ge w hw.2.1]
      rw [hstep]
      exact ih _
  exact hfold D.gates []

theorem pairs (s : Equiv.Perm (Fin 26)) (C : Circuit) : andPairs 26 (rename s C)=andPairs 26 C := by
  have ceq (a b : Nat) : InCone 26 (rename s C) a b ↔ InCone 26 C a b := by
    unfold InCone
    rw [show cones 26 (rename s C)=cones 26 C from relabel_cones s C]
  have lengths : (rename s C).gates.length = C.gates.length := by simp [rename]
  unfold andPairs
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter,lengths,gate_at,gate,ceq]

theorem ok_renamed (s : Equiv.Perm (Fin 26)) (hs : Good s) (C : Circuit) (ok : OK C) :
    OK (rename s C) := by
  obtain ⟨ao,nd,semantic,pos,j,lt,hop,y,on,off⟩ := ok
  obtain ⟨ao',nd'⟩ := preserve_model s C ao nd
  refine ⟨ao',nd',boundary s hs C semantic,by simpa [pairs] using pos,j,by simpa [Circuit.size,rename] using lt,
    by simpa [gate_at,gate] using hop,y ∘ s.symm,?_,?_⟩
  · have z := wires s C (y ∘ s.symm) (26+j)
    rw [rho_internal _ (by omega)] at z
    simpa [z,Function.comp_assoc] using on
  · simpa [eval_renamed,Function.comp_assoc] using off

theorem win_back (s : Equiv.Perm (Fin 26)) (hs : Good s) (C : Circuit) (w : Win (rename s C)) : Win C := by
  obtain ⟨v,hv,once⟩ := w
  have hval : v=0 ∨ v=13 := by simpa using hv
  let z : Fin 26 := ⟨v,by rcases hval with rfl|rfl <;> decide⟩
  let u := s.symm z
  have which : u=0 ∨ u=13 := by
    rcases hs.2 with fixed | swap <;> rcases hval with h|h
    · left;apply s.injective; simpa [u,z,fixed.1] using (show z=0 by apply Fin.ext;exact h)
    · right;apply s.injective; simpa [u,z,fixed.2] using (show z=13 by apply Fin.ext;exact h)
    · right;apply s.injective; simpa [u,z,swap.2] using (show z=0 by apply Fin.ext;exact h)
    · left;apply s.injective; simpa [u,z,swap.1] using (show z=13 by apply Fin.ext;exact h)
  refine ⟨u.val,?_,?_⟩
  · rcases which with h|h <;> simp [h]
  · rw [← scalar s hs C u C.output]
    simpa [u,z,rename] using once

def listed (a b : Fin 26) : Prop := 26 * min a.val b.val + max a.val b.val ∈
    ([1,2,13,14,17,28,29,40,41,43,56,60,66,68] : List ℕ)

theorem listed_of_rep : ∀ a b : Fin 26, (min a b,max a b) ∈ reps → listed a b := by
  unfold listed
  decide +kernel

theorem first_gate (C : Circuit) (cap : C.size≤64) (ok : OK C) :
    ∃ (D : Circuit) (a b : Fin 26) (t : Bool),
      D.size ≤ 63 ∧ listed a b ∧
      let E : Circuit := ⟨⟨if t then GateOp.or else GateOp.and,[a.val,b.val]⟩::D.gates,D.output⟩
      OK E ∧ (Win E → Win C) := by
  have nz : 0 < C.gates.length := by
    obtain ⟨j,hj,_⟩ := ok.2.2.2.2
    change j < C.gates.length at hj
    omega
  obtain ⟨g,gs,hs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos nz)
  have mem : g ∈ C.gates := by simp [hs]
  obtain ⟨i,j,hij⟩ := List.length_eq_two.mp (ok.1.2.2 g mem)
  have first : gateAt C 0 = g := by simp [gateAt,hs]
  have lt_i : i<26 := by simpa using ok.1.2.1 0 nz i (by simp [first,hij])
  have lt_j : j<26 := by simpa using ok.1.2.1 0 nz j (by simp [first,hij])
  let a : Fin 26 := ⟨i,lt_i⟩
  let b : Fin 26 := ⟨j,lt_j⟩
  have diff : a ≠ b := by
    intro eq
    have v : i=j := congrArg Fin.val eq
    have nd := ok.2.1 g mem
    simp [hij,v] at nd
  obtain ⟨s,good,rep⟩ := representatives a b diff
  obtain ⟨t,op⟩ : ∃ t : Bool, (if t then GateOp.or else GateOp.and)=g.op := by
    rcases ok.1.1 g mem with l|r
    · exact ⟨false,l.symm⟩
    · exact ⟨true,r.symm⟩
  let D : Circuit := ⟨gs.map (gate s),rho s C.output⟩
  have budget : D.size≤63 := by
    change C.gates.length≤64 at cap
    simp only [hs,List.length_cons] at cap
    change (List.map (gate s) gs).length≤63
    rw [List.length_map];omega
  have Eeq : (⟨⟨if t then GateOp.or else GateOp.and,[(s a).val,(s b).val]⟩::D.gates,D.output⟩ : Circuit) = rename s C := by
    have ri : rho s i=(s a).val := rho_raw s a
    have rj : rho s j=(s b).val := rho_raw s b
    simp [rename,hs,gate,hij,D,op,ri,rj]
  exact ⟨D,s a,s b,t,budget,listed_of_rep _ _ rep,Eeq ▸ ok_renamed s good C ok,Eeq ▸ win_back s good C⟩

end PEqualNP.Outside.L_meta_17766_aux.Canonical
open PEqualNP.ReadTwo in
theorem PEqualNP.Outside.L_meta_17766 : (have x1 : (Fin ((13 : ℕ) + (13 : ℕ)) → Bool) → Bool := PEqualNP.ReadTwo.fpl (13 : ℕ) fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (∀ (x4 : Fin (26 : ℕ)), x3 x4 = x1 x3 → x1 (Function.update x3 x4 !x3 x4) ≠ x1 x3) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x3 = x1 x3) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x2 ∧ ∃ x3 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x4 : Fin (26 : ℕ) → Bool), PEqualNP.ReadTwo.wval x2 x4 ((26 : ℕ) + x3) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x4 = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x4 ∈ [(0 : ℕ), (13 : ℕ)], (PEqualNP.ReadK.scalarMults x3 (26 : ℕ) [(0 : ℕ), (13 : ℕ)] x4).getD x3.output Option.none = Option.some (1 : ℕ); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x4.size ≤ (64 : ℕ) →     x2 x4 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Fin (26 : ℕ)) (x9 : Fin (26 : ℕ)) (x10 : Bool),         have x11 : PEqualNP.CircuitLowerBounds.Circuit := { gates := { op := if x10 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x8, ↑x9] : PEqualNP.CircuitLowerBounds.Gate } :: x7.gates, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit };         x7.size ≤ (63 : ℕ) ∧ (26 : ℕ) * Min.min ↑x8 ↑x9 + Max.max ↑x8 ↑x9 ∈ [(1 : ℕ), (2 : ℕ), (13 : ℕ), (14 : ℕ), (17 : ℕ), (28 : ℕ), (29 : ℕ), (40 : ℕ), (41 : ℕ), (43 : ℕ), (56 : ℕ), (60 : ℕ), (66 : ℕ), (68 : ℕ)] ∧ x2 x11 ∧ (x3 x11 → x3 x4)) := by
  have eq : fpl 13 (fun (p l : Fin 13) => p-l ∈ ([0,1,3,9] : List (Fin 13))) =
      fpl 13 (fun (p l : Fin 13) => p-l ∈ ({0,1,3,9} : Finset (Fin 13))) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [fpl,decide_eq_true_eq,List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton]
  rw [eq]
  exact PEqualNP.Outside.L_meta_17766_aux.Canonical.first_gate
