import Weak80905Data

namespace PEqualNP.Outside.L_meta_2373.Weak80905
open Live1024 CountVector

def support76616 : Fin 11 → Finset (Fin 13) := ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {9}, {10}, {11}]
lemma support_counts76616 : ∀ i : Fin 11, count tag76616 (support76616 i) = unit i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

def childLabels76616 : Fin 11 → List (Sum (Fin 13) Bool) := ![
  [Sum.inr false, Sum.inr true, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inr false, Sum.inr true, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr false, Sum.inr true, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr false, Sum.inr true, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr false, Sum.inr true, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr false, Sum.inr true, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 12, Sum.inr false, Sum.inr true]
]
def childWs76616 : Fin 11 → List Sig := ![
  [s1, s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864, s13864]
]

lemma childLabels_nodup76616 : ∀ i : Fin 11, (childLabels76616 i).Nodup := by decide +kernel
lemma childLabels_basis76616 : ∀ i : Fin 11, (childLabels76616 i).toFinset =
    duplicateRoots Finset.univ (support76616 i) := by decide +kernel
lemma childLabels_values76616 : ∀ i : Fin 11,
    (childLabels76616 i).map (duplicateRaw (fun r => signal (tag76616 r)) (signal i)) = childWs76616 i := by
  decide +kernel
lemma childLabels_size76616 : ∀ i : Fin 11,
    (duplicateRoots Finset.univ (support76616 i)).card + 1 ≤ 15 := by decide +kernel

def support80905 : Fin 11 → Finset (Fin 12) := ![{0}, {1}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}]
lemma support_counts80905 : ∀ i : Fin 11, count tag80905 (support80905 i) = unit i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

def childLabels80905 : Fin 11 → List (Sum (Fin 12) Bool) := ![
  [Sum.inr false, Sum.inr true, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inr false, Sum.inr true, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr false, Sum.inr true, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr false, Sum.inr true, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr false, Sum.inr true, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr false, Sum.inr true, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr false, Sum.inr true, Sum.inl 9, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 10, Sum.inl 11],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 11, Sum.inr false, Sum.inr true]
]
def childWs80905 : Fin 11 → List Sig := ![
  [s1, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s5, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s6, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s7, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s9, s9, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s10, s13864, s13864],
  [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864, s13864]
]

lemma childLabels_nodup80905 : ∀ i : Fin 11, (childLabels80905 i).Nodup := by decide +kernel
lemma childLabels_basis80905 : ∀ i : Fin 11, (childLabels80905 i).toFinset =
    duplicateRoots Finset.univ (support80905 i) := by decide +kernel
lemma childLabels_values80905 : ∀ i : Fin 11,
    (childLabels80905 i).map (duplicateRaw (fun r => signal (tag80905 r)) (signal i)) = childWs80905 i := by
  decide +kernel
lemma childLabels_size80905 : ∀ i : Fin 11,
    (duplicateRoots Finset.univ (support80905 i)).card + 2 ≤ 15 := by decide +kernel

def gateSupport : Finset (Fin 13) := {7, 11}
def gateVector : Fin 11 → Nat := fun j => unit 7 j + unit 10 j
def gateValue : Fin 2 → Sig := ![s29951, s15934]
def gateLabels : List (Sum (Fin 13) Bool) := [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 12, Sum.inr false]

lemma gateSupport_counts : count tag76616 gateSupport = gateVector := by
  funext j; fin_cases j <;> decide +kernel
lemma gate_table : cuts76616 = List.ofFn (fun i : Fin 2 => (gateVector, gateValue i)) := by decide +kernel
lemma gateLabels_nodup : gateLabels.Nodup := by decide +kernel
lemma gateLabels_basis : gateLabels.toFinset = compressRoots Finset.univ gateSupport := by decide +kernel
lemma gateLabels_size : (compressRoots Finset.univ gateSupport).card + 2 ≤ 14 := by decide +kernel

end PEqualNP.Outside.L_meta_2373.Weak80905
