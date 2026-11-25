import KernelFirstTables
namespace PEqualNP.Outside.L_meta_10760_first
def root13Q : List (Nat × Nat) := pick acc_extraFive [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
lemma root13Q_bounds : ∀ e ∈ root13Q, Imp [] e.1 e.2 := pickI accBounds_extraFive
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root13_checked : okR topC [] root13Q (0, 13) = true := by decide +kernel
lemma bound13 : Imp [] 0 13 := okR_imp topC_ok (Or.inl rfl) root13_checked root13Q_bounds
end PEqualNP.Outside.L_meta_10760_first
