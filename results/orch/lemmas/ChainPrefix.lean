import GateCatalogue
import SymmetryFirst
import KernelFinalRoot
import KernelCase0
import KernelCase1
import KernelCase2
import KernelCase4
import KernelCase5
import KernelSymCase0
import KernelSymCase1
import KernelSymCase2
import KernelSymCase3
import KernelSymCase4
import KernelSymCase5
import KernelSymCase6
import KernelSymCase7
namespace PEqualNP.Outside.L_meta_10760_first
def catalog0 : List Gt := []
lemma catalog0_bounds : ∀ e ∈ catalog0, Imp [e] 0 13 := gate_bounds_nil
lemma certified0 : Imp [gate0] 0 13 :=
  case0_bound bound13
lemma reflected0 : Imp [(false, 3, 5)] 0 13 := by
  apply sym_bound false 3 5 (by decide) (by decide)
  change Imp [(false, 2, 0)] 0 13
  exact imp_gate_swap certified0
def catalog1 : List Gt := catalog0 ++ [gate0, (false, 3, 5)]
lemma catalog1_bounds : ∀ e ∈ catalog1, Imp [e] 0 13 :=
  gate_bounds_append catalog0_bounds (gate_bounds_cons certified0 (gate_bounds_cons reflected0 gate_bounds_nil))
lemma certified1 : Imp [gate1] 0 13 :=
  case1_bound bound13 (gate_bounds_sub catalog1_bounds (by decide))
def catalog2 : List Gt := catalog1 ++ [gate1]
lemma catalog2_bounds : ∀ e ∈ catalog2, Imp [e] 0 13 :=
  gate_bounds_append catalog1_bounds (gate_bounds_cons certified1 gate_bounds_nil)
lemma certified2 : Imp [gate2] 0 13 :=
  case2_bound bound13 (gate_bounds_sub catalog2_bounds (by decide))
lemma reflected2 : Imp [(false, 5, 6)] 0 13 := by
  apply sym_bound false 5 6 (by decide) (by decide)
  change Imp [(false, 0, 6)] 0 13
  exact certified2
def catalog3 : List Gt := catalog2 ++ [gate2, (false, 5, 6)]
lemma catalog3_bounds : ∀ e ∈ catalog3, Imp [e] 0 13 :=
  gate_bounds_append catalog2_bounds (gate_bounds_cons certified2 (gate_bounds_cons reflected2 gate_bounds_nil))
lemma certified3 : Imp [gate4] 0 13 :=
  case4_bound bound13 (gate_bounds_sub catalog3_bounds (by decide))
lemma reflected3 : Imp [(true, 3, 4)] 0 13 := by
  apply sym_bound true 3 4 (by decide) (by decide)
  change Imp [(true, 2, 1)] 0 13
  exact imp_gate_swap certified3
def catalog4 : List Gt := catalog3 ++ [gate4, (true, 3, 4)]
lemma catalog4_bounds : ∀ e ∈ catalog4, Imp [e] 0 13 :=
  gate_bounds_append catalog3_bounds (gate_bounds_cons certified3 (gate_bounds_cons reflected3 gate_bounds_nil))
lemma certified4 : Imp [gate5] 0 13 :=
  case5_bound bound13 (gate_bounds_sub catalog4_bounds (by decide))
def catalog5 : List Gt := catalog4 ++ [gate5]
lemma catalog5_bounds : ∀ e ∈ catalog5, Imp [e] 0 13 :=
  gate_bounds_append catalog4_bounds (gate_bounds_cons certified4 gate_bounds_nil)
lemma certified5 : Imp [gate_s0] 0 13 :=
  case_s0_bound bound13 (gate_bounds_sub catalog5_bounds (by decide))
lemma reflected5 : Imp [(false, 4, 5)] 0 13 := by
  apply sym_bound false 4 5 (by decide) (by decide)
  change Imp [(false, 1, 0)] 0 13
  exact imp_gate_swap certified5
def catalog6 : List Gt := catalog5 ++ [gate_s0, (false, 4, 5)]
lemma catalog6_bounds : ∀ e ∈ catalog6, Imp [e] 0 13 :=
  gate_bounds_append catalog5_bounds (gate_bounds_cons certified5 (gate_bounds_cons reflected5 gate_bounds_nil))
lemma certified6 : Imp [gate_s1] 0 13 :=
  case_s1_bound bound13 (gate_bounds_sub catalog6_bounds (by decide))
lemma reflected6 : Imp [(false, 2, 5)] 0 13 := by
  apply sym_bound false 2 5 (by decide) (by decide)
  change Imp [(false, 3, 0)] 0 13
  exact imp_gate_swap certified6
def catalog7 : List Gt := catalog6 ++ [gate_s1, (false, 2, 5)]
lemma catalog7_bounds : ∀ e ∈ catalog7, Imp [e] 0 13 :=
  gate_bounds_append catalog6_bounds (gate_bounds_cons certified6 (gate_bounds_cons reflected6 gate_bounds_nil))
lemma certified7 : Imp [gate_s2] 0 13 :=
  case_s2_bound bound13 (gate_bounds_sub catalog7_bounds (by decide))
lemma reflected7 : Imp [(false, 3, 4)] 0 13 := by
  apply sym_bound false 3 4 (by decide) (by decide)
  change Imp [(false, 2, 1)] 0 13
  exact imp_gate_swap certified7
def catalog8 : List Gt := catalog7 ++ [gate_s2, (false, 3, 4)]
lemma catalog8_bounds : ∀ e ∈ catalog8, Imp [e] 0 13 :=
  gate_bounds_append catalog7_bounds (gate_bounds_cons certified7 (gate_bounds_cons reflected7 gate_bounds_nil))
lemma certified8 : Imp [gate_s3] 0 13 :=
  case_s3_bound bound13 (gate_bounds_sub catalog8_bounds (by decide))
lemma reflected8 : Imp [(false, 4, 6)] 0 13 := by
  apply sym_bound false 4 6 (by decide) (by decide)
  change Imp [(false, 1, 6)] 0 13
  exact certified8
def catalog9 : List Gt := catalog8 ++ [gate_s3, (false, 4, 6)]
lemma catalog9_bounds : ∀ e ∈ catalog9, Imp [e] 0 13 :=
  gate_bounds_append catalog8_bounds (gate_bounds_cons certified8 (gate_bounds_cons reflected8 gate_bounds_nil))
lemma certified9 : Imp [gate_s4] 0 13 :=
  case_s4_bound bound13 (gate_bounds_sub catalog9_bounds (by decide))
def catalog10 : List Gt := catalog9 ++ [gate_s4]
lemma catalog10_bounds : ∀ e ∈ catalog10, Imp [e] 0 13 :=
  gate_bounds_append catalog9_bounds (gate_bounds_cons certified9 gate_bounds_nil)
lemma certified10 : Imp [gate_s5] 0 13 :=
  case_s5_bound bound13 (gate_bounds_sub catalog10_bounds (by decide))
lemma reflected10 : Imp [(false, 1, 5)] 0 13 := by
  apply sym_bound false 1 5 (by decide) (by decide)
  change Imp [(false, 4, 0)] 0 13
  exact imp_gate_swap certified10
def catalog11 : List Gt := catalog10 ++ [gate_s5, (false, 1, 5)]
lemma catalog11_bounds : ∀ e ∈ catalog11, Imp [e] 0 13 :=
  gate_bounds_append catalog10_bounds (gate_bounds_cons certified10 (gate_bounds_cons reflected10 gate_bounds_nil))
lemma certified11 : Imp [gate_s6] 0 13 :=
  case_s6_bound bound13 (gate_bounds_sub catalog11_bounds (by decide))
lemma reflected11 : Imp [(false, 2, 4)] 0 13 := by
  apply sym_bound false 2 4 (by decide) (by decide)
  change Imp [(false, 3, 1)] 0 13
  exact imp_gate_swap certified11
def catalog12 : List Gt := catalog11 ++ [gate_s6, (false, 2, 4)]
lemma catalog12_bounds : ∀ e ∈ catalog12, Imp [e] 0 13 :=
  gate_bounds_append catalog11_bounds (gate_bounds_cons certified11 (gate_bounds_cons reflected11 gate_bounds_nil))
lemma certified12 : Imp [gate_s7] 0 13 :=
  case_s7_bound bound13 (gate_bounds_sub catalog12_bounds (by decide))
lemma reflected12 : Imp [(false, 3, 6)] 0 13 := by
  apply sym_bound false 3 6 (by decide) (by decide)
  change Imp [(false, 2, 6)] 0 13
  exact certified12
def catalog13 : List Gt := catalog12 ++ [gate_s7, (false, 3, 6)]
lemma catalog13_bounds : ∀ e ∈ catalog13, Imp [e] 0 13 :=
  gate_bounds_append catalog12_bounds (gate_bounds_cons certified12 (gate_bounds_cons reflected12 gate_bounds_nil))
end PEqualNP.Outside.L_meta_10760_first
