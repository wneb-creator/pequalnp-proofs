import CountFixture1098

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098
open Live1024 CountVector

def entryVector (i : Fin 13) : Fin 12 → Nat := (entries.getD i.val ((fun _ => 0), zero)).1
def entryValue (i : Fin 13) : Sig := (entries.getD i.val ((fun _ => 0), zero)).2

def cutVector (i : Fin 13) : Fin 12 → Nat := (cuts.getD i.val ((fun _ => 0), zero)).1
def cutValue (i : Fin 13) : Sig := (cuts.getD i.val ((fun _ => 0), zero)).2

def entrySupport : Fin 13 → Finset (Fin 16) := ![
  {0},
  {2},
  {3},
  {4},
  {7},
  {8},
  {9},
  {10},
  {11},
  {12},
  {13},
  {14},
  {0, 4}
]

lemma entrySupport_counts : ∀ i : Fin 13, count basisTag (entrySupport i) = entryVector i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

def cutSupport : Fin 13 → Finset (Fin 16) := ![
  {0, 4},
  {4, 13},
  {4, 13},
  {0, 14},
  {0, 14},
  {4, 14},
  {4, 14},
  {13, 14},
  {13, 14},
  {0, 4, 13},
  {0, 4, 13},
  {0, 4, 14},
  {0, 4, 14}
]

lemma cutSupport_counts : ∀ i : Fin 13, count basisTag (cutSupport i) = cutVector i := by
  intro i; fin_cases i <;> funext j <;> fin_cases j <;> decide +kernel

lemma entry_table : entries = List.ofFn (fun i : Fin 13 => (entryVector i, entryValue i)) := by
  decide +kernel

lemma cut_table : cuts = List.ofFn (fun i : Fin 13 => (cutVector i, cutValue i)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2373.CountFixture1098
