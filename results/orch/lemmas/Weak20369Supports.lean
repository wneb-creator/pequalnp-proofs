import Weak20369Data

namespace PEqualNP.Outside.L_meta_2373.Weak20369
open Live1024 CountVector

def entryVector9611 (i : Fin 12) : Fin 11 → Nat := (entries9611.getD i.val ((fun _ => 0), zero)).1
def entryValue9611 (i : Fin 12) : Sig := (entries9611.getD i.val ((fun _ => 0), zero)).2
def support9611 : Fin 12 → Finset (Fin 14) := ![{0}, {2}, {3}, {5}, {6}, {7}, {8}, {9}, {10}, {11}, {12}, {0, 3}]
lemma entry_table9611 : entries9611 = List.ofFn (fun i : Fin 12 => (entryVector9611 i, entryValue9611 i)) := by decide +kernel
lemma support_counts9611 : ∀ i : Fin 12, count tag9611 (support9611 i) = entryVector9611 i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

def childLabels9611 : Fin 12 → List (Sum (Fin 14) Bool) := ![
  [Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inr false, Sum.inr true, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr false, Sum.inr true, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr false, Sum.inr true, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr false, Sum.inr true, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr false, Sum.inr true, Sum.inl 11, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inr false, Sum.inr true, Sum.inl 12, Sum.inl 13],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 13, Sum.inr false, Sum.inr true],
  [Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inr false, Sum.inr true, Sum.inl 11, Sum.inl 12, Sum.inl 13]
]
def childWs9611 : Fin 12 → List Sig := ![
  [s1, s1, s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s2, s3, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s5, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s6, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s7, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s8, s8, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s9, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s1761, s1761, s7093, s7093],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093, s7093],
  [s1, s2, s3, s4, s5, s6, s7, s8, s9, s28, s28, s1761, s7093, s7093]
]
def childCap9611 : Fin 12 → Nat := ![14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 13]

lemma childLabels_nodup9611 : ∀ i : Fin 12, (childLabels9611 i).Nodup := by decide +kernel
lemma childLabels_basis9611 : ∀ i : Fin 12, (childLabels9611 i).toFinset =
    duplicateRoots Finset.univ (support9611 i) := by decide +kernel
lemma childLabels_values9611 : ∀ i : Fin 12,
    (childLabels9611 i).map (duplicateRaw (fun r => signal9611 (tag9611 r)) (entryValue9611 i)) = childWs9611 i := by
  decide +kernel
lemma childLabels_size9611 : ∀ i : Fin 12,
    (duplicateRoots Finset.univ (support9611 i)).card + 0 ≤ childCap9611 i + 1 := by decide +kernel

def gateVector (i : Fin 5) : Fin 11 → Nat := (cuts9611.getD i.val ((fun _ => 0), zero)).1
def gateValue (i : Fin 5) : Sig := (cuts9611.getD i.val ((fun _ => 0), zero)).2
def gateSupport : Fin 5 → Finset (Fin 14) := ![{0, 3}, {3, 12}, {3, 12}, {0, 3, 12}, {0, 3, 12}]
def gateCap : Fin 5 → Nat := ![13, 13, 13, 12, 12]
def gateLabels : Fin 5 → List (Sum (Fin 14) Bool) := ![
  [Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inr false],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 13, Sum.inr false],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 13, Sum.inr false],
  [Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 13, Sum.inr false],
  [Sum.inl 1, Sum.inl 2, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 13, Sum.inr false]
]
lemma gate_table : cuts9611 = List.ofFn (fun i : Fin 5 => (gateVector i, gateValue i)) := by decide +kernel
lemma gateSupport_counts : ∀ i : Fin 5, count tag9611 (gateSupport i) = gateVector i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel
lemma gateLabels_nodup : ∀ i : Fin 5, (gateLabels i).Nodup := by decide +kernel
lemma gateLabels_basis : ∀ i : Fin 5, (gateLabels i).toFinset = compressRoots Finset.univ (gateSupport i) := by decide +kernel
lemma gateLabels_size : ∀ i : Fin 5, (compressRoots Finset.univ (gateSupport i)).card + 1 ≤ gateCap i + 1 := by decide +kernel

def entryVector20369 (i : Fin 11) : Fin 11 → Nat := (entries20369.getD i.val ((fun _ => 0), zero)).1
def entryValue20369 (i : Fin 11) : Sig := (entries20369.getD i.val ((fun _ => 0), zero)).2
def support20369 : Fin 11 → Finset (Fin 13) := ![{0}, {2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {10}, {11}]
lemma entry_table20369 : entries20369 = List.ofFn (fun i : Fin 11 => (entryVector20369 i, entryValue20369 i)) := by decide +kernel
lemma support_counts20369 : ∀ i : Fin 11, count tag20369 (support20369 i) = entryVector20369 i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

def childLabels20369 : Fin 11 → List (Sum (Fin 13) Bool) := ![
  [Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr false, Sum.inr true, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr false, Sum.inr true, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inr false, Sum.inr true, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inr false, Sum.inr true, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr false, Sum.inr true, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr false, Sum.inr true, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 10, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr false, Sum.inr true, Sum.inl 11, Sum.inl 12],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 12, Sum.inr false, Sum.inr true]
]
def childWs20369 : Fin 11 → List Sig := ![
  [s1, s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s5, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s6, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s7, s7, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s7, s9, s9, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s10, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s1477, s6015, s6015],
  [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015, s6015]
]
def childCap20369 : Fin 11 → Nat := ![14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14]

lemma childLabels_nodup20369 : ∀ i : Fin 11, (childLabels20369 i).Nodup := by decide +kernel
lemma childLabels_basis20369 : ∀ i : Fin 11, (childLabels20369 i).toFinset =
    duplicateRoots Finset.univ (support20369 i) := by decide +kernel
lemma childLabels_values20369 : ∀ i : Fin 11,
    (childLabels20369 i).map (duplicateRaw (fun r => signal20369 (tag20369 r)) (entryValue20369 i)) = childWs20369 i := by
  decide +kernel
lemma childLabels_size20369 : ∀ i : Fin 11,
    (duplicateRoots Finset.univ (support20369 i)).card + 1 ≤ childCap20369 i + 1 := by decide +kernel

end PEqualNP.Outside.L_meta_2373.Weak20369
