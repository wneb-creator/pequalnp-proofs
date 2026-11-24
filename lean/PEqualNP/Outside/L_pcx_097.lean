import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_097_aux

open PEqualNP.ProofComplexity

def Bounded {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ) (C : Clause V) :=
  ∃ p, IsDerivation F p ∧ C ∈ p ∧ ∀ D ∈ p, D.card ≤ w

lemma append_deriv {V : Type} [DecidableEq V] {F : Set (Clause V)} {p q : List (Clause V)}
    (hp : IsDerivation F p) (hq : IsDerivation F q) : IsDerivation F (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ hc ih => exact ih.ax hc
  | res _ hc hd hr ih =>
    exact ih.res (List.mem_append_left _ hc) (List.mem_append_left _ hd) hr

lemma ax_line {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} {C : Clause V}
    (hc : C ∈ F) (hw : C.card ≤ w) : Bounded F w C :=
  ⟨[C], IsDerivation.nil.ax hc, by simp, by simpa using hw⟩

lemma res_line {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ} {C D R : Clause V}
    (hC : Bounded F w C) (hD : Bounded F w D) (v : V) (hp : (v,true) ∈ C)
    (hn : (v,false) ∈ D) (he : R = C.erase (v,true) ∪ D.erase (v,false))
    (hw : R.card ≤ w) : Bounded F w R := by
  obtain ⟨p,dp,hc,wp⟩ := hC
  obtain ⟨q,dq,hd,wq⟩ := hD
  refine ⟨R :: (p ++ q), (append_deriv dp dq).res (List.mem_append_left q hc)
    (List.mem_append_right p hd) ⟨v,hp,hn,he⟩, by simp, ?_⟩
  intro S hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hw
  · rcases List.mem_append.mp hs with h | h
    · exact wp _ h
    · exact wq _ h

lemma no_narrow {V : Type} [DecidableEq V] {F : Set (Clause V)} {w : ℕ}
    (h : ∀ C ∈ F, C.card ≤ w → ∃ v, (v,false) ∈ C) :
    ¬ ∃ p, IsRefutation F p ∧ ∀ D ∈ p, D.card ≤ w := by
  rintro ⟨p,⟨dp,empty⟩,wp⟩
  suffices hh : ∀ C ∈ p, ∃ v, (v,false) ∈ C by simpa using hh ∅ empty
  clear empty
  induction dp with
  | nil => simp
  | ax dp hc ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hm
    · exact h _ hc (wp _ (by simp))
    · exact ih (fun D hD => wp D (List.mem_cons_of_mem _ hD)) _ hm
  | res dp hC hD hr ih =>
    have hh := ih (fun D hD => wp D (List.mem_cons_of_mem _ hD))
    intro S hS
    rcases List.mem_cons.mp hS with rfl | hm
    · obtain ⟨v,hv⟩ := hh _ hC
      obtain ⟨a,_,_,rfl⟩ := hr
      exact ⟨v, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp,hv⟩)⟩
    · exact hh _ hm

abbrev V3 := ((Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3)))
abbrev v3_1 : V3 := ((3,∅),((0,false),(0,0)))
abbrev v3_2 : V3 := ((2,∅),((0,false),(0,0)))
abbrev v3_3 : V3 := ((2,∅),((0,false),(0,1)))
abbrev v3_4 : V3 := ((2,∅),((0,false),(0,2)))
abbrev v3_5 : V3 := ((7,{0,1}),((0,false),(0,0)))
abbrev v3_6 : V3 := ((6,{0,1}),((0,false),(0,0)))
abbrev v3_7 : V3 := ((5,{0,1}),((0,false),(0,0)))
abbrev v3_8 : V3 := ((0,∅),((0,false),(0,0)))
abbrev v3_9 : V3 := ((0,∅),((0,false),(0,1)))
abbrev v3_10 : V3 := ((5,{0,1}),((0,true),(0,0)))
abbrev v3_11 : V3 := ((0,∅),((0,true),(0,0)))
abbrev v3_12 : V3 := ((0,∅),((0,true),(0,1)))
abbrev v3_13 : V3 := ((7,{0,2}),((0,false),(0,0)))
abbrev v3_14 : V3 := ((6,{0,2}),((0,false),(0,0)))
abbrev v3_15 : V3 := ((5,{0,2}),((0,false),(0,0)))
abbrev v3_16 : V3 := ((0,∅),((0,false),(0,2)))
abbrev v3_17 : V3 := ((5,{0,2}),((0,true),(0,0)))
abbrev v3_18 : V3 := ((0,∅),((0,true),(0,2)))
abbrev v3_19 : V3 := ((7,{1,2}),((0,false),(0,0)))
abbrev v3_20 : V3 := ((6,{1,2}),((0,false),(0,0)))
abbrev v3_21 : V3 := ((5,{1,2}),((0,false),(0,0)))
abbrev v3_22 : V3 := ((5,{1,2}),((0,true),(0,0)))
abbrev v3_23 : V3 := ((6,{0}),((0,false),(0,0)))
abbrev v3_24 : V3 := ((5,{0}),((0,false),(0,0)))
abbrev v3_25 : V3 := ((5,{0}),((0,true),(0,0)))
abbrev v3_26 : V3 := ((6,{1}),((0,false),(0,0)))
abbrev v3_27 : V3 := ((5,{1}),((0,false),(0,0)))
abbrev v3_28 : V3 := ((5,{1}),((0,true),(0,0)))
abbrev v3_29 : V3 := ((6,{2}),((0,false),(0,0)))
abbrev v3_30 : V3 := ((5,{2}),((0,false),(0,0)))
abbrev v3_31 : V3 := ((5,{2}),((0,true),(0,0)))
lemma upper3 (F : Set (Clause V3))
    (ax0 : {(v3_2,false)} ∈ F)
    (ax1 : {(v3_3,false)} ∈ F)
    (ax2 : {(v3_4,false)} ∈ F)
    (ax3 : {(v3_2,true),(v3_3,true),(v3_5,true)} ∈ F)
    (ax6 : {(v3_5,false),(v3_1,true)} ∈ F)
    (ax8 : {(v3_5,false),(v3_6,true)} ∈ F)
    (ax10 : {(v3_6,false),(v3_7,true)} ∈ F)
    (ax12 : {(v3_7,false),(v3_8,true),(v3_9,true)} ∈ F)
    (ax14 : {(v3_6,false),(v3_10,true)} ∈ F)
    (ax16 : {(v3_10,false),(v3_11,true),(v3_12,true)} ∈ F)
    (ax18 : {(v3_2,true),(v3_4,true),(v3_13,true)} ∈ F)
    (ax21 : {(v3_13,false),(v3_14,true)} ∈ F)
    (ax23 : {(v3_14,false),(v3_15,true)} ∈ F)
    (ax25 : {(v3_15,false),(v3_8,true),(v3_16,true)} ∈ F)
    (ax27 : {(v3_14,false),(v3_17,true)} ∈ F)
    (ax29 : {(v3_17,false),(v3_11,true),(v3_18,true)} ∈ F)
    (ax31 : {(v3_3,true),(v3_4,true),(v3_19,true)} ∈ F)
    (ax34 : {(v3_19,false),(v3_20,true)} ∈ F)
    (ax36 : {(v3_20,false),(v3_21,true)} ∈ F)
    (ax38 : {(v3_21,false),(v3_9,true),(v3_16,true)} ∈ F)
    (ax40 : {(v3_20,false),(v3_22,true)} ∈ F)
    (ax42 : {(v3_22,false),(v3_12,true),(v3_18,true)} ∈ F)
    (ax44 : {(v3_23,false),(v3_1,false)} ∈ F)
    (ax46 : {(v3_25,false),(v3_24,false),(v3_23,true)} ∈ F)
    (ax48 : {(v3_8,false),(v3_24,true)} ∈ F)
    (ax50 : {(v3_11,false),(v3_25,true)} ∈ F)
    (ax52 : {(v3_26,false),(v3_1,false)} ∈ F)
    (ax54 : {(v3_28,false),(v3_27,false),(v3_26,true)} ∈ F)
    (ax56 : {(v3_9,false),(v3_27,true)} ∈ F)
    (ax58 : {(v3_12,false),(v3_28,true)} ∈ F)
    (ax60 : {(v3_29,false),(v3_1,false)} ∈ F)
    (ax62 : {(v3_31,false),(v3_30,false),(v3_29,true)} ∈ F)
    (ax64 : {(v3_16,false),(v3_30,true)} ∈ F)
    (ax66 : {(v3_18,false),(v3_31,true)} ∈ F)
    : ∃ p, IsRefutation F p ∧ ∀ D ∈ p, D.card ≤ 3 := by
  have l3_0 : Bounded F 3 {(v3_2,false)} := ax_line ax0 (by decide)
  have l3_1 : Bounded F 3 {(v3_3,false)} := ax_line ax1 (by decide)
  have l3_2 : Bounded F 3 {(v3_4,false)} := ax_line ax2 (by decide)
  have l3_3 : Bounded F 3 {(v3_2,true),(v3_3,true),(v3_5,true)} := ax_line ax3 (by decide)
  have l3_4 : Bounded F 3 {(v3_3,true),(v3_5,true)} := res_line l3_3 l3_0 v3_2 (by decide) (by decide) (by decide) (by decide)
  have l3_5 : Bounded F 3 {(v3_5,true)} := res_line l3_4 l3_1 v3_3 (by decide) (by decide) (by decide) (by decide)
  have l3_6 : Bounded F 3 {(v3_5,false),(v3_1,true)} := ax_line ax6 (by decide)
  have l3_7 : Bounded F 3 {(v3_1,true)} := res_line l3_5 l3_6 v3_5 (by decide) (by decide) (by decide) (by decide)
  have l3_8 : Bounded F 3 {(v3_5,false),(v3_6,true)} := ax_line ax8 (by decide)
  have l3_9 : Bounded F 3 {(v3_6,true)} := res_line l3_5 l3_8 v3_5 (by decide) (by decide) (by decide) (by decide)
  have l3_10 : Bounded F 3 {(v3_6,false),(v3_7,true)} := ax_line ax10 (by decide)
  have l3_11 : Bounded F 3 {(v3_7,true)} := res_line l3_9 l3_10 v3_6 (by decide) (by decide) (by decide) (by decide)
  have l3_12 : Bounded F 3 {(v3_7,false),(v3_8,true),(v3_9,true)} := ax_line ax12 (by decide)
  have l3_13 : Bounded F 3 {(v3_8,true),(v3_9,true)} := res_line l3_11 l3_12 v3_7 (by decide) (by decide) (by decide) (by decide)
  have l3_14 : Bounded F 3 {(v3_6,false),(v3_10,true)} := ax_line ax14 (by decide)
  have l3_15 : Bounded F 3 {(v3_10,true)} := res_line l3_9 l3_14 v3_6 (by decide) (by decide) (by decide) (by decide)
  have l3_16 : Bounded F 3 {(v3_10,false),(v3_11,true),(v3_12,true)} := ax_line ax16 (by decide)
  have l3_17 : Bounded F 3 {(v3_11,true),(v3_12,true)} := res_line l3_15 l3_16 v3_10 (by decide) (by decide) (by decide) (by decide)
  have l3_18 : Bounded F 3 {(v3_2,true),(v3_4,true),(v3_13,true)} := ax_line ax18 (by decide)
  have l3_19 : Bounded F 3 {(v3_4,true),(v3_13,true)} := res_line l3_18 l3_0 v3_2 (by decide) (by decide) (by decide) (by decide)
  have l3_20 : Bounded F 3 {(v3_13,true)} := res_line l3_19 l3_2 v3_4 (by decide) (by decide) (by decide) (by decide)
  have l3_21 : Bounded F 3 {(v3_13,false),(v3_14,true)} := ax_line ax21 (by decide)
  have l3_22 : Bounded F 3 {(v3_14,true)} := res_line l3_20 l3_21 v3_13 (by decide) (by decide) (by decide) (by decide)
  have l3_23 : Bounded F 3 {(v3_14,false),(v3_15,true)} := ax_line ax23 (by decide)
  have l3_24 : Bounded F 3 {(v3_15,true)} := res_line l3_22 l3_23 v3_14 (by decide) (by decide) (by decide) (by decide)
  have l3_25 : Bounded F 3 {(v3_15,false),(v3_8,true),(v3_16,true)} := ax_line ax25 (by decide)
  have l3_26 : Bounded F 3 {(v3_8,true),(v3_16,true)} := res_line l3_24 l3_25 v3_15 (by decide) (by decide) (by decide) (by decide)
  have l3_27 : Bounded F 3 {(v3_14,false),(v3_17,true)} := ax_line ax27 (by decide)
  have l3_28 : Bounded F 3 {(v3_17,true)} := res_line l3_22 l3_27 v3_14 (by decide) (by decide) (by decide) (by decide)
  have l3_29 : Bounded F 3 {(v3_17,false),(v3_11,true),(v3_18,true)} := ax_line ax29 (by decide)
  have l3_30 : Bounded F 3 {(v3_11,true),(v3_18,true)} := res_line l3_28 l3_29 v3_17 (by decide) (by decide) (by decide) (by decide)
  have l3_31 : Bounded F 3 {(v3_3,true),(v3_4,true),(v3_19,true)} := ax_line ax31 (by decide)
  have l3_32 : Bounded F 3 {(v3_4,true),(v3_19,true)} := res_line l3_31 l3_1 v3_3 (by decide) (by decide) (by decide) (by decide)
  have l3_33 : Bounded F 3 {(v3_19,true)} := res_line l3_32 l3_2 v3_4 (by decide) (by decide) (by decide) (by decide)
  have l3_34 : Bounded F 3 {(v3_19,false),(v3_20,true)} := ax_line ax34 (by decide)
  have l3_35 : Bounded F 3 {(v3_20,true)} := res_line l3_33 l3_34 v3_19 (by decide) (by decide) (by decide) (by decide)
  have l3_36 : Bounded F 3 {(v3_20,false),(v3_21,true)} := ax_line ax36 (by decide)
  have l3_37 : Bounded F 3 {(v3_21,true)} := res_line l3_35 l3_36 v3_20 (by decide) (by decide) (by decide) (by decide)
  have l3_38 : Bounded F 3 {(v3_21,false),(v3_9,true),(v3_16,true)} := ax_line ax38 (by decide)
  have l3_39 : Bounded F 3 {(v3_9,true),(v3_16,true)} := res_line l3_37 l3_38 v3_21 (by decide) (by decide) (by decide) (by decide)
  have l3_40 : Bounded F 3 {(v3_20,false),(v3_22,true)} := ax_line ax40 (by decide)
  have l3_41 : Bounded F 3 {(v3_22,true)} := res_line l3_35 l3_40 v3_20 (by decide) (by decide) (by decide) (by decide)
  have l3_42 : Bounded F 3 {(v3_22,false),(v3_12,true),(v3_18,true)} := ax_line ax42 (by decide)
  have l3_43 : Bounded F 3 {(v3_12,true),(v3_18,true)} := res_line l3_41 l3_42 v3_22 (by decide) (by decide) (by decide) (by decide)
  have l3_44 : Bounded F 3 {(v3_23,false),(v3_1,false)} := ax_line ax44 (by decide)
  have l3_45 : Bounded F 3 {(v3_23,false)} := res_line l3_7 l3_44 v3_1 (by decide) (by decide) (by decide) (by decide)
  have l3_46 : Bounded F 3 {(v3_25,false),(v3_24,false),(v3_23,true)} := ax_line ax46 (by decide)
  have l3_47 : Bounded F 3 {(v3_25,false),(v3_24,false)} := res_line l3_46 l3_45 v3_23 (by decide) (by decide) (by decide) (by decide)
  have l3_48 : Bounded F 3 {(v3_8,false),(v3_24,true)} := ax_line ax48 (by decide)
  have l3_49 : Bounded F 3 {(v3_25,false),(v3_8,false)} := res_line l3_48 l3_47 v3_24 (by decide) (by decide) (by decide) (by decide)
  have l3_50 : Bounded F 3 {(v3_11,false),(v3_25,true)} := ax_line ax50 (by decide)
  have l3_51 : Bounded F 3 {(v3_11,false),(v3_8,false)} := res_line l3_50 l3_49 v3_25 (by decide) (by decide) (by decide) (by decide)
  have l3_52 : Bounded F 3 {(v3_26,false),(v3_1,false)} := ax_line ax52 (by decide)
  have l3_53 : Bounded F 3 {(v3_26,false)} := res_line l3_7 l3_52 v3_1 (by decide) (by decide) (by decide) (by decide)
  have l3_54 : Bounded F 3 {(v3_28,false),(v3_27,false),(v3_26,true)} := ax_line ax54 (by decide)
  have l3_55 : Bounded F 3 {(v3_28,false),(v3_27,false)} := res_line l3_54 l3_53 v3_26 (by decide) (by decide) (by decide) (by decide)
  have l3_56 : Bounded F 3 {(v3_9,false),(v3_27,true)} := ax_line ax56 (by decide)
  have l3_57 : Bounded F 3 {(v3_28,false),(v3_9,false)} := res_line l3_56 l3_55 v3_27 (by decide) (by decide) (by decide) (by decide)
  have l3_58 : Bounded F 3 {(v3_12,false),(v3_28,true)} := ax_line ax58 (by decide)
  have l3_59 : Bounded F 3 {(v3_12,false),(v3_9,false)} := res_line l3_58 l3_57 v3_28 (by decide) (by decide) (by decide) (by decide)
  have l3_60 : Bounded F 3 {(v3_29,false),(v3_1,false)} := ax_line ax60 (by decide)
  have l3_61 : Bounded F 3 {(v3_29,false)} := res_line l3_7 l3_60 v3_1 (by decide) (by decide) (by decide) (by decide)
  have l3_62 : Bounded F 3 {(v3_31,false),(v3_30,false),(v3_29,true)} := ax_line ax62 (by decide)
  have l3_63 : Bounded F 3 {(v3_31,false),(v3_30,false)} := res_line l3_62 l3_61 v3_29 (by decide) (by decide) (by decide) (by decide)
  have l3_64 : Bounded F 3 {(v3_16,false),(v3_30,true)} := ax_line ax64 (by decide)
  have l3_65 : Bounded F 3 {(v3_31,false),(v3_16,false)} := res_line l3_64 l3_63 v3_30 (by decide) (by decide) (by decide) (by decide)
  have l3_66 : Bounded F 3 {(v3_18,false),(v3_31,true)} := ax_line ax66 (by decide)
  have l3_67 : Bounded F 3 {(v3_18,false),(v3_16,false)} := res_line l3_66 l3_65 v3_31 (by decide) (by decide) (by decide) (by decide)
  have l3_68 : Bounded F 3 {(v3_9,false),(v3_11,true)} := res_line l3_17 l3_59 v3_12 (by decide) (by decide) (by decide) (by decide)
  have l3_69 : Bounded F 3 {(v3_18,false),(v3_8,true)} := res_line l3_26 l3_67 v3_16 (by decide) (by decide) (by decide) (by decide)
  have l3_70 : Bounded F 3 {(v3_8,false),(v3_18,true)} := res_line l3_30 l3_51 v3_11 (by decide) (by decide) (by decide) (by decide)
  have l3_71 : Bounded F 3 {(v3_18,false),(v3_9,true)} := res_line l3_39 l3_67 v3_16 (by decide) (by decide) (by decide) (by decide)
  have l3_72 : Bounded F 3 {(v3_9,false),(v3_18,true)} := res_line l3_43 l3_59 v3_12 (by decide) (by decide) (by decide) (by decide)
  have l3_73 : Bounded F 3 {(v3_9,false),(v3_8,false)} := res_line l3_68 l3_51 v3_11 (by decide) (by decide) (by decide) (by decide)
  have l3_74 : Bounded F 3 {(v3_9,false),(v3_8,true)} := res_line l3_72 l3_69 v3_18 (by decide) (by decide) (by decide) (by decide)
  have l3_75 : Bounded F 3 {(v3_8,false),(v3_9,true)} := res_line l3_70 l3_71 v3_18 (by decide) (by decide) (by decide) (by decide)
  have l3_76 : Bounded F 3 {(v3_8,true)} := res_line l3_13 l3_74 v3_9 (by decide) (by decide) (by decide) (by decide)
  have l3_77 : Bounded F 3 {(v3_8,false)} := res_line l3_75 l3_73 v3_9 (by decide) (by decide) (by decide) (by decide)
  have l3_78 : Bounded F 3 ∅ := res_line l3_76 l3_77 v3_8 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p,hd,he,hw⟩ := l3_78
  exact ⟨p,⟨hd,he⟩,hw⟩
abbrev V4 := ((Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4)))
abbrev v4_1 : V4 := ((3,∅),((0,false),(0,0)))
abbrev v4_2 : V4 := ((2,∅),((0,false),(0,0)))
abbrev v4_3 : V4 := ((2,∅),((0,false),(0,1)))
abbrev v4_4 : V4 := ((2,∅),((0,false),(0,2)))
abbrev v4_5 : V4 := ((2,∅),((0,false),(0,3)))
abbrev v4_6 : V4 := ((7,{0,1,2}),((0,false),(0,0)))
abbrev v4_7 : V4 := ((6,{0,1,2}),((0,false),(0,0)))
abbrev v4_8 : V4 := ((5,{0,1,2}),((0,false),(0,0)))
abbrev v4_9 : V4 := ((0,∅),((0,false),(0,0)))
abbrev v4_10 : V4 := ((0,∅),((0,false),(0,1)))
abbrev v4_11 : V4 := ((0,∅),((0,false),(0,2)))
abbrev v4_12 : V4 := ((5,{0,1,2}),((0,true),(0,0)))
abbrev v4_13 : V4 := ((0,∅),((0,true),(0,0)))
abbrev v4_14 : V4 := ((0,∅),((0,true),(0,1)))
abbrev v4_15 : V4 := ((0,∅),((0,true),(0,2)))
abbrev v4_16 : V4 := ((7,{0,1,3}),((0,false),(0,0)))
abbrev v4_17 : V4 := ((6,{0,1,3}),((0,false),(0,0)))
abbrev v4_18 : V4 := ((5,{0,1,3}),((0,false),(0,0)))
abbrev v4_19 : V4 := ((0,∅),((0,false),(0,3)))
abbrev v4_20 : V4 := ((5,{0,1,3}),((0,true),(0,0)))
abbrev v4_21 : V4 := ((0,∅),((0,true),(0,3)))
abbrev v4_22 : V4 := ((7,{0,2,3}),((0,false),(0,0)))
abbrev v4_23 : V4 := ((6,{0,2,3}),((0,false),(0,0)))
abbrev v4_24 : V4 := ((5,{0,2,3}),((0,false),(0,0)))
abbrev v4_25 : V4 := ((5,{0,2,3}),((0,true),(0,0)))
abbrev v4_26 : V4 := ((7,{1,2,3}),((0,false),(0,0)))
abbrev v4_27 : V4 := ((6,{1,2,3}),((0,false),(0,0)))
abbrev v4_28 : V4 := ((5,{1,2,3}),((0,false),(0,0)))
abbrev v4_29 : V4 := ((5,{1,2,3}),((0,true),(0,0)))
abbrev v4_30 : V4 := ((6,{0,2}),((0,false),(0,0)))
abbrev v4_31 : V4 := ((5,{0,2}),((0,false),(0,0)))
abbrev v4_32 : V4 := ((5,{0,2}),((0,true),(0,0)))
abbrev v4_33 : V4 := ((6,{0,3}),((0,false),(0,0)))
abbrev v4_34 : V4 := ((5,{0,3}),((0,false),(0,0)))
abbrev v4_35 : V4 := ((5,{0,3}),((0,true),(0,0)))
abbrev v4_36 : V4 := ((6,{1,3}),((0,false),(0,0)))
abbrev v4_37 : V4 := ((5,{1,3}),((0,false),(0,0)))
abbrev v4_38 : V4 := ((5,{1,3}),((0,true),(0,0)))
lemma upper4 (F : Set (Clause V4))
    (ax0 : {(v4_2,false)} ∈ F)
    (ax1 : {(v4_3,false)} ∈ F)
    (ax2 : {(v4_4,false)} ∈ F)
    (ax3 : {(v4_5,false)} ∈ F)
    (ax4 : {(v4_2,true),(v4_3,true),(v4_4,true),(v4_6,true)} ∈ F)
    (ax8 : {(v4_6,false),(v4_1,true)} ∈ F)
    (ax10 : {(v4_6,false),(v4_7,true)} ∈ F)
    (ax12 : {(v4_7,false),(v4_8,true)} ∈ F)
    (ax14 : {(v4_8,false),(v4_9,true),(v4_10,true),(v4_11,true)} ∈ F)
    (ax16 : {(v4_2,true),(v4_3,true),(v4_5,true),(v4_16,true)} ∈ F)
    (ax20 : {(v4_16,false),(v4_17,true)} ∈ F)
    (ax22 : {(v4_17,false),(v4_18,true)} ∈ F)
    (ax24 : {(v4_18,false),(v4_9,true),(v4_10,true),(v4_19,true)} ∈ F)
    (ax26 : {(v4_17,false),(v4_20,true)} ∈ F)
    (ax28 : {(v4_20,false),(v4_13,true),(v4_14,true),(v4_21,true)} ∈ F)
    (ax30 : {(v4_2,true),(v4_4,true),(v4_5,true),(v4_22,true)} ∈ F)
    (ax34 : {(v4_22,false),(v4_23,true)} ∈ F)
    (ax36 : {(v4_23,false),(v4_24,true)} ∈ F)
    (ax38 : {(v4_24,false),(v4_9,true),(v4_11,true),(v4_19,true)} ∈ F)
    (ax40 : {(v4_23,false),(v4_25,true)} ∈ F)
    (ax42 : {(v4_25,false),(v4_13,true),(v4_15,true),(v4_21,true)} ∈ F)
    (ax44 : {(v4_30,false),(v4_1,false)} ∈ F)
    (ax46 : {(v4_32,false),(v4_31,false),(v4_30,true)} ∈ F)
    (ax48 : {(v4_9,false),(v4_31,true)} ∈ F)
    (ax50 : {(v4_13,false),(v4_32,true)} ∈ F)
    (ax52 : {(v4_15,false),(v4_32,true)} ∈ F)
    (ax54 : {(v4_11,false),(v4_31,true)} ∈ F)
    (ax58 : {(v4_33,false),(v4_1,false)} ∈ F)
    (ax60 : {(v4_35,false),(v4_34,false),(v4_33,true)} ∈ F)
    (ax62 : {(v4_9,false),(v4_34,true)} ∈ F)
    (ax64 : {(v4_13,false),(v4_35,true)} ∈ F)
    (ax65 : {(v4_21,false),(v4_35,true)} ∈ F)
    (ax67 : {(v4_19,false),(v4_34,true)} ∈ F)
    (ax71 : {(v4_36,false),(v4_1,false)} ∈ F)
    (ax73 : {(v4_38,false),(v4_37,false),(v4_36,true)} ∈ F)
    (ax75 : {(v4_10,false),(v4_37,true)} ∈ F)
    (ax77 : {(v4_14,false),(v4_38,true)} ∈ F)
    (ax79 : {(v4_21,false),(v4_38,true)} ∈ F)
    : ∃ p, IsRefutation F p ∧ ∀ D ∈ p, D.card ≤ 4 := by
  have l4_0 : Bounded F 4 {(v4_2,false)} := ax_line ax0 (by decide)
  have l4_1 : Bounded F 4 {(v4_3,false)} := ax_line ax1 (by decide)
  have l4_2 : Bounded F 4 {(v4_4,false)} := ax_line ax2 (by decide)
  have l4_3 : Bounded F 4 {(v4_5,false)} := ax_line ax3 (by decide)
  have l4_4 : Bounded F 4 {(v4_2,true),(v4_3,true),(v4_4,true),(v4_6,true)} := ax_line ax4 (by decide)
  have l4_5 : Bounded F 4 {(v4_3,true),(v4_4,true),(v4_6,true)} := res_line l4_4 l4_0 v4_2 (by decide) (by decide) (by decide) (by decide)
  have l4_6 : Bounded F 4 {(v4_4,true),(v4_6,true)} := res_line l4_5 l4_1 v4_3 (by decide) (by decide) (by decide) (by decide)
  have l4_7 : Bounded F 4 {(v4_6,true)} := res_line l4_6 l4_2 v4_4 (by decide) (by decide) (by decide) (by decide)
  have l4_8 : Bounded F 4 {(v4_6,false),(v4_1,true)} := ax_line ax8 (by decide)
  have l4_9 : Bounded F 4 {(v4_1,true)} := res_line l4_7 l4_8 v4_6 (by decide) (by decide) (by decide) (by decide)
  have l4_10 : Bounded F 4 {(v4_6,false),(v4_7,true)} := ax_line ax10 (by decide)
  have l4_11 : Bounded F 4 {(v4_7,true)} := res_line l4_7 l4_10 v4_6 (by decide) (by decide) (by decide) (by decide)
  have l4_12 : Bounded F 4 {(v4_7,false),(v4_8,true)} := ax_line ax12 (by decide)
  have l4_13 : Bounded F 4 {(v4_8,true)} := res_line l4_11 l4_12 v4_7 (by decide) (by decide) (by decide) (by decide)
  have l4_14 : Bounded F 4 {(v4_8,false),(v4_9,true),(v4_10,true),(v4_11,true)} := ax_line ax14 (by decide)
  have l4_15 : Bounded F 4 {(v4_9,true),(v4_10,true),(v4_11,true)} := res_line l4_13 l4_14 v4_8 (by decide) (by decide) (by decide) (by decide)
  have l4_16 : Bounded F 4 {(v4_2,true),(v4_3,true),(v4_5,true),(v4_16,true)} := ax_line ax16 (by decide)
  have l4_17 : Bounded F 4 {(v4_3,true),(v4_5,true),(v4_16,true)} := res_line l4_16 l4_0 v4_2 (by decide) (by decide) (by decide) (by decide)
  have l4_18 : Bounded F 4 {(v4_5,true),(v4_16,true)} := res_line l4_17 l4_1 v4_3 (by decide) (by decide) (by decide) (by decide)
  have l4_19 : Bounded F 4 {(v4_16,true)} := res_line l4_18 l4_3 v4_5 (by decide) (by decide) (by decide) (by decide)
  have l4_20 : Bounded F 4 {(v4_16,false),(v4_17,true)} := ax_line ax20 (by decide)
  have l4_21 : Bounded F 4 {(v4_17,true)} := res_line l4_19 l4_20 v4_16 (by decide) (by decide) (by decide) (by decide)
  have l4_22 : Bounded F 4 {(v4_17,false),(v4_18,true)} := ax_line ax22 (by decide)
  have l4_23 : Bounded F 4 {(v4_18,true)} := res_line l4_21 l4_22 v4_17 (by decide) (by decide) (by decide) (by decide)
  have l4_24 : Bounded F 4 {(v4_18,false),(v4_9,true),(v4_10,true),(v4_19,true)} := ax_line ax24 (by decide)
  have l4_25 : Bounded F 4 {(v4_9,true),(v4_10,true),(v4_19,true)} := res_line l4_23 l4_24 v4_18 (by decide) (by decide) (by decide) (by decide)
  have l4_26 : Bounded F 4 {(v4_17,false),(v4_20,true)} := ax_line ax26 (by decide)
  have l4_27 : Bounded F 4 {(v4_20,true)} := res_line l4_21 l4_26 v4_17 (by decide) (by decide) (by decide) (by decide)
  have l4_28 : Bounded F 4 {(v4_20,false),(v4_13,true),(v4_14,true),(v4_21,true)} := ax_line ax28 (by decide)
  have l4_29 : Bounded F 4 {(v4_13,true),(v4_14,true),(v4_21,true)} := res_line l4_27 l4_28 v4_20 (by decide) (by decide) (by decide) (by decide)
  have l4_30 : Bounded F 4 {(v4_2,true),(v4_4,true),(v4_5,true),(v4_22,true)} := ax_line ax30 (by decide)
  have l4_31 : Bounded F 4 {(v4_4,true),(v4_5,true),(v4_22,true)} := res_line l4_30 l4_0 v4_2 (by decide) (by decide) (by decide) (by decide)
  have l4_32 : Bounded F 4 {(v4_5,true),(v4_22,true)} := res_line l4_31 l4_2 v4_4 (by decide) (by decide) (by decide) (by decide)
  have l4_33 : Bounded F 4 {(v4_22,true)} := res_line l4_32 l4_3 v4_5 (by decide) (by decide) (by decide) (by decide)
  have l4_34 : Bounded F 4 {(v4_22,false),(v4_23,true)} := ax_line ax34 (by decide)
  have l4_35 : Bounded F 4 {(v4_23,true)} := res_line l4_33 l4_34 v4_22 (by decide) (by decide) (by decide) (by decide)
  have l4_36 : Bounded F 4 {(v4_23,false),(v4_24,true)} := ax_line ax36 (by decide)
  have l4_37 : Bounded F 4 {(v4_24,true)} := res_line l4_35 l4_36 v4_23 (by decide) (by decide) (by decide) (by decide)
  have l4_38 : Bounded F 4 {(v4_24,false),(v4_9,true),(v4_11,true),(v4_19,true)} := ax_line ax38 (by decide)
  have l4_39 : Bounded F 4 {(v4_9,true),(v4_11,true),(v4_19,true)} := res_line l4_37 l4_38 v4_24 (by decide) (by decide) (by decide) (by decide)
  have l4_40 : Bounded F 4 {(v4_23,false),(v4_25,true)} := ax_line ax40 (by decide)
  have l4_41 : Bounded F 4 {(v4_25,true)} := res_line l4_35 l4_40 v4_23 (by decide) (by decide) (by decide) (by decide)
  have l4_42 : Bounded F 4 {(v4_25,false),(v4_13,true),(v4_15,true),(v4_21,true)} := ax_line ax42 (by decide)
  have l4_43 : Bounded F 4 {(v4_13,true),(v4_15,true),(v4_21,true)} := res_line l4_41 l4_42 v4_25 (by decide) (by decide) (by decide) (by decide)
  have l4_44 : Bounded F 4 {(v4_30,false),(v4_1,false)} := ax_line ax44 (by decide)
  have l4_45 : Bounded F 4 {(v4_30,false)} := res_line l4_9 l4_44 v4_1 (by decide) (by decide) (by decide) (by decide)
  have l4_46 : Bounded F 4 {(v4_32,false),(v4_31,false),(v4_30,true)} := ax_line ax46 (by decide)
  have l4_47 : Bounded F 4 {(v4_32,false),(v4_31,false)} := res_line l4_46 l4_45 v4_30 (by decide) (by decide) (by decide) (by decide)
  have l4_48 : Bounded F 4 {(v4_9,false),(v4_31,true)} := ax_line ax48 (by decide)
  have l4_49 : Bounded F 4 {(v4_32,false),(v4_9,false)} := res_line l4_48 l4_47 v4_31 (by decide) (by decide) (by decide) (by decide)
  have l4_50 : Bounded F 4 {(v4_13,false),(v4_32,true)} := ax_line ax50 (by decide)
  have l4_51 : Bounded F 4 {(v4_13,false),(v4_9,false)} := res_line l4_50 l4_49 v4_32 (by decide) (by decide) (by decide) (by decide)
  have l4_52 : Bounded F 4 {(v4_15,false),(v4_32,true)} := ax_line ax52 (by decide)
  have l4_53 : Bounded F 4 {(v4_15,false),(v4_9,false)} := res_line l4_52 l4_49 v4_32 (by decide) (by decide) (by decide) (by decide)
  have l4_54 : Bounded F 4 {(v4_11,false),(v4_31,true)} := ax_line ax54 (by decide)
  have l4_55 : Bounded F 4 {(v4_32,false),(v4_11,false)} := res_line l4_54 l4_47 v4_31 (by decide) (by decide) (by decide) (by decide)
  have l4_56 : Bounded F 4 {(v4_13,false),(v4_11,false)} := res_line l4_50 l4_55 v4_32 (by decide) (by decide) (by decide) (by decide)
  have l4_57 : Bounded F 4 {(v4_15,false),(v4_11,false)} := res_line l4_52 l4_55 v4_32 (by decide) (by decide) (by decide) (by decide)
  have l4_58 : Bounded F 4 {(v4_33,false),(v4_1,false)} := ax_line ax58 (by decide)
  have l4_59 : Bounded F 4 {(v4_33,false)} := res_line l4_9 l4_58 v4_1 (by decide) (by decide) (by decide) (by decide)
  have l4_60 : Bounded F 4 {(v4_35,false),(v4_34,false),(v4_33,true)} := ax_line ax60 (by decide)
  have l4_61 : Bounded F 4 {(v4_35,false),(v4_34,false)} := res_line l4_60 l4_59 v4_33 (by decide) (by decide) (by decide) (by decide)
  have l4_62 : Bounded F 4 {(v4_9,false),(v4_34,true)} := ax_line ax62 (by decide)
  have l4_63 : Bounded F 4 {(v4_35,false),(v4_9,false)} := res_line l4_62 l4_61 v4_34 (by decide) (by decide) (by decide) (by decide)
  have l4_64 : Bounded F 4 {(v4_13,false),(v4_35,true)} := ax_line ax64 (by decide)
  have l4_65 : Bounded F 4 {(v4_21,false),(v4_35,true)} := ax_line ax65 (by decide)
  have l4_66 : Bounded F 4 {(v4_21,false),(v4_9,false)} := res_line l4_65 l4_63 v4_35 (by decide) (by decide) (by decide) (by decide)
  have l4_67 : Bounded F 4 {(v4_19,false),(v4_34,true)} := ax_line ax67 (by decide)
  have l4_68 : Bounded F 4 {(v4_35,false),(v4_19,false)} := res_line l4_67 l4_61 v4_34 (by decide) (by decide) (by decide) (by decide)
  have l4_69 : Bounded F 4 {(v4_19,false),(v4_13,false)} := res_line l4_64 l4_68 v4_35 (by decide) (by decide) (by decide) (by decide)
  have l4_70 : Bounded F 4 {(v4_21,false),(v4_19,false)} := res_line l4_65 l4_68 v4_35 (by decide) (by decide) (by decide) (by decide)
  have l4_71 : Bounded F 4 {(v4_36,false),(v4_1,false)} := ax_line ax71 (by decide)
  have l4_72 : Bounded F 4 {(v4_36,false)} := res_line l4_9 l4_71 v4_1 (by decide) (by decide) (by decide) (by decide)
  have l4_73 : Bounded F 4 {(v4_38,false),(v4_37,false),(v4_36,true)} := ax_line ax73 (by decide)
  have l4_74 : Bounded F 4 {(v4_38,false),(v4_37,false)} := res_line l4_73 l4_72 v4_36 (by decide) (by decide) (by decide) (by decide)
  have l4_75 : Bounded F 4 {(v4_10,false),(v4_37,true)} := ax_line ax75 (by decide)
  have l4_76 : Bounded F 4 {(v4_38,false),(v4_10,false)} := res_line l4_75 l4_74 v4_37 (by decide) (by decide) (by decide) (by decide)
  have l4_77 : Bounded F 4 {(v4_14,false),(v4_38,true)} := ax_line ax77 (by decide)
  have l4_78 : Bounded F 4 {(v4_14,false),(v4_10,false)} := res_line l4_77 l4_76 v4_38 (by decide) (by decide) (by decide) (by decide)
  have l4_79 : Bounded F 4 {(v4_21,false),(v4_38,true)} := ax_line ax79 (by decide)
  have l4_80 : Bounded F 4 {(v4_21,false),(v4_10,false)} := res_line l4_79 l4_76 v4_38 (by decide) (by decide) (by decide) (by decide)
  have l4_81 : Bounded F 4 {(v4_11,false),(v4_13,true),(v4_21,true)} := res_line l4_43 l4_57 v4_15 (by decide) (by decide) (by decide) (by decide)
  have l4_82 : Bounded F 4 {(v4_9,false),(v4_13,true),(v4_15,true)} := res_line l4_43 l4_66 v4_21 (by decide) (by decide) (by decide) (by decide)
  have l4_83 : Bounded F 4 {(v4_13,false),(v4_9,true),(v4_11,true)} := res_line l4_39 l4_69 v4_19 (by decide) (by decide) (by decide) (by decide)
  have l4_84 : Bounded F 4 {(v4_10,false),(v4_13,true),(v4_21,true)} := res_line l4_29 l4_78 v4_14 (by decide) (by decide) (by decide) (by decide)
  have l4_85 : Bounded F 4 {(v4_21,false),(v4_9,true),(v4_19,true)} := res_line l4_25 l4_80 v4_10 (by decide) (by decide) (by decide) (by decide)
  have l4_86 : Bounded F 4 {(v4_9,false),(v4_13,true)} := res_line l4_82 l4_53 v4_15 (by decide) (by decide) (by decide) (by decide)
  have l4_87 : Bounded F 4 {(v4_11,false),(v4_21,true)} := res_line l4_81 l4_56 v4_13 (by decide) (by decide) (by decide) (by decide)
  have l4_88 : Bounded F 4 {(v4_13,false),(v4_9,true)} := res_line l4_83 l4_56 v4_11 (by decide) (by decide) (by decide) (by decide)
  have l4_89 : Bounded F 4 {(v4_21,false),(v4_9,true)} := res_line l4_85 l4_70 v4_19 (by decide) (by decide) (by decide) (by decide)
  have l4_90 : Bounded F 4 {(v4_9,true),(v4_11,true),(v4_13,true),(v4_21,true)} := res_line l4_15 l4_84 v4_10 (by decide) (by decide) (by decide) (by decide)
  have l4_91 : Bounded F 4 {(v4_9,false)} := res_line l4_86 l4_51 v4_13 (by decide) (by decide) (by decide) (by decide)
  have l4_92 : Bounded F 4 {(v4_13,false)} := res_line l4_88 l4_51 v4_9 (by decide) (by decide) (by decide) (by decide)
  have l4_93 : Bounded F 4 {(v4_21,false)} := res_line l4_89 l4_66 v4_9 (by decide) (by decide) (by decide) (by decide)
  have l4_94 : Bounded F 4 {(v4_9,true),(v4_13,true),(v4_21,true)} := res_line l4_90 l4_87 v4_11 (by decide) (by decide) (by decide) (by decide)
  have l4_95 : Bounded F 4 {(v4_9,true),(v4_13,true)} := res_line l4_94 l4_93 v4_21 (by decide) (by decide) (by decide) (by decide)
  have l4_96 : Bounded F 4 {(v4_9,true)} := res_line l4_95 l4_92 v4_13 (by decide) (by decide) (by decide) (by decide)
  have l4_97 : Bounded F 4 ∅ := res_line l4_96 l4_91 v4_9 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p,hd,he,hw⟩ := l4_97
  exact ⟨p,⟨hd,he⟩,hw⟩
end PEqualNP.Outside.L_pcx_097_aux
open PEqualNP.Outside.L_pcx_097_aux
open PEqualNP.ProofComplexity
set_option maxRecDepth 16000 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_pcx_097 : (∀ Ma : Finset (Fin 3) → Prop, (∀ Yma : Finset (Fin 3), Ma Yma ↔ ((∀ uma ∈ Yma, ∀ wma ∈ Yma, ¬ uma ≠ wma) ∧ ∀ zma : Fin 3, zma ∉ Yma → ∃ yma ∈ Yma, yma ≠ zma)) → ∀ Qa : Finset (Fin 3) → Prop, (∀ Yqa : Finset (Fin 3), Qa Yqa ↔ ∃ Iqa : Finset (Fin 3), Ma Iqa ∧ ∃ wqa : Fin 3, wqa ∉ Iqa ∧ Yqa = insert wqa Iqa) → ∀ Fa : Set (PEqualNP.ProofComplexity.Clause ((Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3)))), Fa = {C1a | ∃ (X1a : Finset (Fin 3)) (i1a : Fin 1) (e1a : Bool) (j1a : Fin 1), (Ma X1a ∨ Qa X1a) ∧ j1a < i1a ∧ (C1a = {((((4, X1a), ((i1a, e1a), (j1a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((1, ∅), ((i1a, e1a), (j1a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)} ∨ C1a = {((((4, X1a), ((i1a, e1a), (j1a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((6, X1a), ((j1a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)} ∨ C1a = {((((4, X1a), ((i1a, e1a), (j1a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true), ((((1, ∅), ((i1a, e1a), (j1a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((6, X1a), ((j1a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)})} ∪ {C2a | ∃ (X2a : Finset (Fin 3)) (i2a : Fin 1) (e2a : Bool), (Ma X2a ∨ Qa X2a) ∧ C2a = insert ((((5, X2a), ((i2a, e2a), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false) (X2a.image (fun v2a : Fin 3 => ((((0, ∅), ((i2a, e2a), (0, v2a))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)) ∪ (Finset.univ.filter (fun j2a : Fin 1 => j2a < i2a)).image (fun k2a : Fin 1 => ((((4, X2a), ((i2a, e2a), (k2a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)))} ∪ {C3a | ∃ (X3a : Finset (Fin 3)) (i3a : Fin 1) (e3a : Bool) (v3a : Fin 3), (Ma X3a ∨ Qa X3a) ∧ v3a ∈ X3a ∧ C3a = {((((5, X3a), ((i3a, e3a), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true), ((((0, ∅), ((i3a, e3a), (0, v3a))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)}} ∪ {C4a | ∃ (X4a : Finset (Fin 3)) (i4a : Fin 1) (e4a : Bool) (j4a : Fin 1), (Ma X4a ∨ Qa X4a) ∧ j4a < i4a ∧ C4a = {((((5, X4a), ((i4a, e4a), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true), ((((4, X4a), ((i4a, e4a), (j4a, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)}} ∪ {C5a | ∃ (X5a : Finset (Fin 3)) (i5a : Fin 1), (Ma X5a ∨ Qa X5a) ∧ (C5a = {((((6, X5a), ((i5a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((5, X5a), ((i5a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)} ∨ C5a = {((((6, X5a), ((i5a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((5, X5a), ((i5a, true), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)} ∨ C5a = {((((6, X5a), ((i5a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true), ((((5, X5a), ((i5a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((5, X5a), ((i5a, true), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)})} ∪ {C6a | ∃ (X6a : Finset (Fin 3)) (v6a : Fin 3), Ma X6a ∧ v6a ∈ X6a ∧ C6a = {((((2, ∅), ((0, false), (0, v6a))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)}} ∪ {C7a | ∃ (X7a : Finset (Fin 3)) (i7a : Fin 1), Ma X7a ∧ C7a = {((((3, ∅), ((i7a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((6, X7a), ((i7a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false)}} ∪ {C8a | ∃ (X8a : Finset (Fin 3)) (i8a : Fin 1), Qa X8a ∧ (C8a = {((((7, X8a), ((i8a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((3, ∅), ((i8a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)} ∨ C8a = {((((7, X8a), ((i8a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), false), ((((6, X8a), ((i8a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)})} ∪ {C9a | ∃ X9a : Finset (Fin 3), Qa X9a ∧ C9a = X9a.image (fun v9a : Fin 3 => ((((2, ∅), ((0, false), (0, v9a))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true)) ∪ Finset.univ.image (fun i9a : Fin 1 => ((((7, X9a), ((i9a, false), (0, 0))) : (Fin 8 × Finset (Fin 3)) × ((Fin 1 × Bool) × (Fin 1 × Fin 3))), true))} → (∃ πa1, PEqualNP.ProofComplexity.IsRefutation Fa πa1 ∧ ∀ Da1 ∈ πa1, Da1.card ≤ 3) ∧ ¬ (∃ πa2, PEqualNP.ProofComplexity.IsRefutation Fa πa2 ∧ ∀ Da2 ∈ πa2, Da2.card ≤ 2)) ∧ (∀ Mb : Finset (Fin 4) → Prop, (∀ Ymb : Finset (Fin 4), Mb Ymb ↔ ((∀ umb ∈ Ymb, ∀ wmb ∈ Ymb, ¬ (umb.val + 1 = wmb.val ∨ wmb.val + 1 = umb.val)) ∧ ∀ zmb : Fin 4, zmb ∉ Ymb → ∃ ymb ∈ Ymb, (ymb.val + 1 = zmb.val ∨ zmb.val + 1 = ymb.val))) → ∀ Qb : Finset (Fin 4) → Prop, (∀ Yqb : Finset (Fin 4), Qb Yqb ↔ ∃ Iqb : Finset (Fin 4), Mb Iqb ∧ ∃ wqb : Fin 4, wqb ∉ Iqb ∧ Yqb = insert wqb Iqb) → ∀ Fb : Set (PEqualNP.ProofComplexity.Clause ((Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4)))), Fb = {C1b | ∃ (X1b : Finset (Fin 4)) (i1b : Fin 1) (e1b : Bool) (j1b : Fin 1), (Mb X1b ∨ Qb X1b) ∧ j1b < i1b ∧ (C1b = {((((4, X1b), ((i1b, e1b), (j1b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((1, ∅), ((i1b, e1b), (j1b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)} ∨ C1b = {((((4, X1b), ((i1b, e1b), (j1b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((6, X1b), ((j1b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)} ∨ C1b = {((((4, X1b), ((i1b, e1b), (j1b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true), ((((1, ∅), ((i1b, e1b), (j1b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((6, X1b), ((j1b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)})} ∪ {C2b | ∃ (X2b : Finset (Fin 4)) (i2b : Fin 1) (e2b : Bool), (Mb X2b ∨ Qb X2b) ∧ C2b = insert ((((5, X2b), ((i2b, e2b), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false) (X2b.image (fun v2b : Fin 4 => ((((0, ∅), ((i2b, e2b), (0, v2b))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)) ∪ (Finset.univ.filter (fun j2b : Fin 1 => j2b < i2b)).image (fun k2b : Fin 1 => ((((4, X2b), ((i2b, e2b), (k2b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)))} ∪ {C3b | ∃ (X3b : Finset (Fin 4)) (i3b : Fin 1) (e3b : Bool) (v3b : Fin 4), (Mb X3b ∨ Qb X3b) ∧ v3b ∈ X3b ∧ C3b = {((((5, X3b), ((i3b, e3b), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true), ((((0, ∅), ((i3b, e3b), (0, v3b))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)}} ∪ {C4b | ∃ (X4b : Finset (Fin 4)) (i4b : Fin 1) (e4b : Bool) (j4b : Fin 1), (Mb X4b ∨ Qb X4b) ∧ j4b < i4b ∧ C4b = {((((5, X4b), ((i4b, e4b), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true), ((((4, X4b), ((i4b, e4b), (j4b, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)}} ∪ {C5b | ∃ (X5b : Finset (Fin 4)) (i5b : Fin 1), (Mb X5b ∨ Qb X5b) ∧ (C5b = {((((6, X5b), ((i5b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((5, X5b), ((i5b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)} ∨ C5b = {((((6, X5b), ((i5b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((5, X5b), ((i5b, true), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)} ∨ C5b = {((((6, X5b), ((i5b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true), ((((5, X5b), ((i5b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((5, X5b), ((i5b, true), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)})} ∪ {C6b | ∃ (X6b : Finset (Fin 4)) (v6b : Fin 4), Mb X6b ∧ v6b ∈ X6b ∧ C6b = {((((2, ∅), ((0, false), (0, v6b))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)}} ∪ {C7b | ∃ (X7b : Finset (Fin 4)) (i7b : Fin 1), Mb X7b ∧ C7b = {((((3, ∅), ((i7b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((6, X7b), ((i7b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false)}} ∪ {C8b | ∃ (X8b : Finset (Fin 4)) (i8b : Fin 1), Qb X8b ∧ (C8b = {((((7, X8b), ((i8b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((3, ∅), ((i8b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)} ∨ C8b = {((((7, X8b), ((i8b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), false), ((((6, X8b), ((i8b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)})} ∪ {C9b | ∃ X9b : Finset (Fin 4), Qb X9b ∧ C9b = X9b.image (fun v9b : Fin 4 => ((((2, ∅), ((0, false), (0, v9b))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true)) ∪ Finset.univ.image (fun i9b : Fin 1 => ((((7, X9b), ((i9b, false), (0, 0))) : (Fin 8 × Finset (Fin 4)) × ((Fin 1 × Bool) × (Fin 1 × Fin 4))), true))} → (∃ πb1, PEqualNP.ProofComplexity.IsRefutation Fb πb1 ∧ ∀ Db1 ∈ πb1, Db1.card ≤ 4) ∧ ¬ (∃ πb2, PEqualNP.ProofComplexity.IsRefutation Fb πb2 ∧ ∀ Db2 ∈ πb2, Db2.card ≤ 3)) := by
  constructor
  · intro M hM Q hQ F hF
    constructor
    · apply upper3
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{0}, 0, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{1}, 1, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{2}, 2, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inr (⟨{0,1}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,1}, 0, by simp only [hQ,hM]; decide, Or.inl (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,1}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inr (Or.inl (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1}, 0, true, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inr (⟨{0,2}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,2}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inr (Or.inl (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, true, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inr (⟨{1,2}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{1,2}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,2}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,2}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,2}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inr (Or.inl (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,2}, 0, true, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{0}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0}, 0, false, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0}, 0, true, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{1}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1}, 0, false, 1, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1}, 0, true, 1, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{2}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{2}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{2}, 0, false, 2, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{2}, 0, true, 2, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
    · apply no_narrow
      intro C hC hw
      rw [hF] at hC
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hC
      rcases hC with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
      · obtain ⟨_,i,_,j,_,lt,_⟩ := h
        exact (lt_irrefl i (Subsingleton.elim j i ▸ lt)).elim
      · obtain ⟨_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨_,_,_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · obtain ⟨_,_,_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · obtain ⟨_,_,_,h|h|h⟩ := h <;> subst C
        · exact ⟨_,Finset.mem_insert_self _ _⟩
        · exact ⟨_,Finset.mem_insert_self _ _⟩
        · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
      · obtain ⟨_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_singleton_self _⟩
      · obtain ⟨_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨_,_,_,h|h⟩ := h <;> subst C <;> exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨X,hX,rfl⟩ := h
        simp only [hQ,hM] at hX
        exfalso
        revert hX hw
        revert X
        decide
  · intro M hM Q hQ F hF
    constructor
    · apply upper4
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,3}, 1, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 2, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 3, by rw [hM]; decide, by decide, by decide⟩))))
      · rw [hF]
        exact Or.inr (⟨{0,1,2}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,1,2}, 0, by simp only [hQ,hM]; decide, Or.inl (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,1,2}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,2}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,2}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inr (⟨{0,1,3}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,1,3}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,3}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,3}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,3}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inr (Or.inl (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,1,3}, 0, true, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inr (⟨{0,2,3}, by simp only [hQ,hM]; decide, by decide⟩)
      · rw [hF]
        exact Or.inl (Or.inr (⟨{0,2,3}, 0, by simp only [hQ,hM]; decide, Or.inr (by decide)⟩))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2,3}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inl (by decide)⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2,3}, 0, false, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2,3}, 0, Or.inr (by simp only [hQ,hM]; decide), Or.inr (Or.inl (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2,3}, 0, true, Or.inr (by simp only [hQ,hM]; decide), by decide⟩))))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, false, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, true, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, true, 2, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,2}, 0, false, 2, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, false, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, true, 0, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, true, 3, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{0,3}, 0, false, 3, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inr (⟨{1,3}, 0, by rw [hM]; decide, by decide⟩)))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,3}, 0, Or.inl (by rw [hM]; decide), Or.inr (Or.inr (by decide))⟩)))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,3}, 0, false, 1, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,3}, 0, true, 1, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
      · rw [hF]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (⟨{1,3}, 0, true, 3, Or.inl (by rw [hM]; decide), by decide, by decide⟩)))))))
    · apply no_narrow
      intro C hC hw
      rw [hF] at hC
      simp only [Set.mem_union, Set.mem_ofPred_eq] at hC
      rcases hC with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
      · obtain ⟨_,i,_,j,_,lt,_⟩ := h
        exact (lt_irrefl i (Subsingleton.elim j i ▸ lt)).elim
      · obtain ⟨_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨_,_,_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · obtain ⟨_,_,_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · obtain ⟨_,_,_,h|h|h⟩ := h <;> subst C
        · exact ⟨_,Finset.mem_insert_self _ _⟩
        · exact ⟨_,Finset.mem_insert_self _ _⟩
        · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
      · obtain ⟨_,_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_singleton_self _⟩
      · obtain ⟨_,_,_,rfl⟩ := h
        exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨_,_,_,h|h⟩ := h <;> subst C <;> exact ⟨_,Finset.mem_insert_self _ _⟩
      · obtain ⟨X,hX,rfl⟩ := h
        simp only [hQ,hM] at hX
        exfalso
        revert hX hw
        revert X
        decide
