import KernelFirstEngine
namespace PEqualNP.Outside.L_meta_10760_first
def zero5 : List (Nat × Nat) := [(122, 1), (117, 1), (110, 1), (109, 1), (107, 1), (94, 1), (93, 1), (87, 1), (62, 1), (59, 1), (55, 1), (31, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_zero5 : zero5.all (fun e => okR topC [] (pr [] e.1) e) = true := by decide +kernel
lemma bounds_zero5 : ∀ e ∈ zero5, Imp [] e.1 e.2 := okAll topC_ok cert_zero5 (by simp)
def acc_zero5 : List (Nat × Nat) := zero5 ++ []
lemma accBounds_zero5 : ∀ e ∈ acc_zero5, Imp [] e.1 e.2 := apI bounds_zero5 (by simp)
def zero4 : List (Nat × Nat) := [(120, 1), (116, 1), (114, 1), (113, 1), (108, 2), (106, 4), (105, 2), (102, 1), (101, 2), (99, 1), (92, 2), (90, 2), (89, 1), (86, 2), (85, 4), (83, 1), (78, 2), (77, 2), (75, 1), (71, 1), (60, 1), (58, 4), (57, 1), (54, 2), (53, 2), (51, 2), (46, 2), (45, 1), (43, 2), (39, 1), (30, 4), (29, 2), (27, 2), (23, 4), (15, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_zero4 : zero4.all (fun e => okR topC [] (pr acc_zero5 e.1) e) = true := by decide +kernel
lemma bounds_zero4 : ∀ e ∈ zero4, Imp [] e.1 e.2 := okAll topC_ok cert_zero4 accBounds_zero5
def acc_zero4 : List (Nat × Nat) := zero4 ++ acc_zero5
lemma accBounds_zero4 : ∀ e ∈ acc_zero4, Imp [] e.1 e.2 := apI bounds_zero4 accBounds_zero5
def zero3 : List (Nat × Nat) := [(112, 3), (104, 5), (100, 4), (98, 4), (97, 4), (88, 4), (84, 5), (82, 4), (81, 4), (76, 3), (74, 5), (73, 4), (70, 4), (69, 5), (67, 3), (56, 4), (52, 4), (50, 5), (49, 4), (44, 4), (42, 5), (41, 4), (38, 4), (37, 4), (35, 4), (28, 5), (26, 5), (25, 4), (22, 5), (21, 5), (19, 5), (14, 5), (13, 4), (11, 4), (7, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_zero3 : zero3.all (fun e => okR topC [] (pr acc_zero4 e.1) e) = true := by decide +kernel
lemma bounds_zero3 : ∀ e ∈ zero3, Imp [] e.1 e.2 := okAll topC_ok cert_zero3 accBounds_zero4
def acc_zero3 : List (Nat × Nat) := zero3 ++ acc_zero4
lemma accBounds_zero3 : ∀ e ∈ acc_zero3, Imp [] e.1 e.2 := apI bounds_zero3 accBounds_zero4
def zero2 : List (Nat × Nat) := [(96, 7), (80, 7), (72, 6), (68, 6), (66, 7), (65, 7), (48, 7), (40, 7), (36, 7), (34, 7), (33, 7), (24, 7), (20, 7), (18, 7), (17, 7), (12, 6), (10, 7), (9, 7), (6, 7), (5, 7), (3, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_zero2 : zero2.all (fun e => okR topC [] (pr acc_zero3 e.1) e) = true := by decide +kernel
lemma bounds_zero2 : ∀ e ∈ zero2, Imp [] e.1 e.2 := okAll topC_ok cert_zero2 accBounds_zero3
def acc_zero2 : List (Nat × Nat) := zero2 ++ acc_zero3
lemma accBounds_zero2 : ∀ e ∈ acc_zero2, Imp [] e.1 e.2 := apI bounds_zero2 accBounds_zero3
def zero1 : List (Nat × Nat) := [(64, 9), (32, 10), (16, 10), (8, 10), (4, 10), (2, 10), (1, 10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_zero1 : zero1.all (fun e => okR topC [] (pr acc_zero2 e.1) e) = true := by decide +kernel
lemma bounds_zero1 : ∀ e ∈ zero1, Imp [] e.1 e.2 := okAll topC_ok cert_zero1 accBounds_zero2
def acc_zero1 : List (Nat × Nat) := zero1 ++ acc_zero2
lemma accBounds_zero1 : ∀ e ∈ acc_zero1, Imp [] e.1 e.2 := apI bounds_zero1 accBounds_zero2
def mixedCandidates : List (Nat × Nat) := [(32800, 4), (32784, 3), (32776, 4), (32772, 4), (32770, 3), (32769, 4), (16448, 4), (16400, 3), (16392, 4), (16388, 3), (16386, 4), (16385, 4), (8256, 4), (8224, 4), (8200, 4), (8196, 6), (8194, 6), (8193, 6), (4160, 6), (4128, 6), (4112, 4), (4100, 4), (4098, 6), (4097, 4), (2112, 6), (2080, 4), (2064, 6), (2056, 4), (2050, 4), (2049, 6), (1088, 4), (1056, 6), (1040, 6), (1032, 6), (1028, 4), (1025, 4), (576, 4), (544, 4), (528, 4), (520, 3), (516, 4), (514, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_mixedCandidates : mixedCandidates.all (fun e => okR topC [] (pr acc_zero1 e.1) e) = true := by decide +kernel
lemma bounds_mixedCandidates : ∀ e ∈ mixedCandidates, Imp [] e.1 e.2 := okAll topC_ok cert_mixedCandidates accBounds_zero1
def acc_mixedCandidates : List (Nat × Nat) := mixedCandidates ++ acc_zero1
lemma accBounds_mixedCandidates : ∀ e ∈ acc_mixedCandidates, Imp [] e.1 e.2 := apI bounds_mixedCandidates accBounds_zero1
def oneCandidates : List (Nat × Nat) := [(32768, 5), (16384, 5), (8192, 7), (4096, 7), (2048, 7), (1024, 7), (512, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_oneCandidates : oneCandidates.all (fun e => okR topC [] (pr acc_mixedCandidates e.1) e) = true := by decide +kernel
lemma bounds_oneCandidates : ∀ e ∈ oneCandidates, Imp [] e.1 e.2 := okAll topC_ok cert_oneCandidates accBounds_mixedCandidates
def acc_oneCandidates : List (Nat × Nat) := oneCandidates ++ acc_mixedCandidates
lemma accBounds_oneCandidates : ∀ e ∈ acc_oneCandidates, Imp [] e.1 e.2 := apI bounds_oneCandidates accBounds_mixedCandidates
def doubleOne : List (Nat × Nat) := [(40960, 4), (24576, 4), (12288, 4), (18432, 4), (6144, 4), (33792, 4), (3072, 4), (4608, 4), (1536, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_doubleOne : doubleOne.all (fun e => okR topC [] (pr acc_oneCandidates e.1) e) = true := by decide +kernel
lemma bounds_doubleOne : ∀ e ∈ doubleOne, Imp [] e.1 e.2 := okAll topC_ok cert_doubleOne accBounds_oneCandidates
def acc_doubleOne : List (Nat × Nat) := doubleOne ++ acc_oneCandidates
lemma accBounds_doubleOne : ∀ e ∈ acc_doubleOne, Imp [] e.1 e.2 := apI bounds_doubleOne accBounds_oneCandidates
def extraFour : List (Nat × Nat) := [(8199, 4), (4194, 4), (2129, 4), (1080, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_extraFour : extraFour.all (fun e => okR topC [] (pr acc_doubleOne e.1) e) = true := by decide +kernel
lemma bounds_extraFour : ∀ e ∈ extraFour, Imp [] e.1 e.2 := okAll topC_ok cert_extraFour accBounds_doubleOne
def acc_extraFour : List (Nat × Nat) := extraFour ++ acc_doubleOne
lemma accBounds_extraFour : ∀ e ∈ acc_extraFour, Imp [] e.1 e.2 := apI bounds_extraFour accBounds_doubleOne
def extraFive : List (Nat × Nat) := [(8198, 5), (8197, 5), (8195, 5), (4192, 5), (4162, 5), (4130, 5), (2128, 5), (2113, 5), (2065, 5), (1072, 5), (1064, 5), (1048, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert_extraFive : extraFive.all (fun e => okR topC [] (pr acc_extraFour e.1) e) = true := by decide +kernel
lemma bounds_extraFive : ∀ e ∈ extraFive, Imp [] e.1 e.2 := okAll topC_ok cert_extraFive accBounds_extraFour
def acc_extraFive : List (Nat × Nat) := extraFive ++ acc_extraFour
lemma accBounds_extraFive : ∀ e ∈ acc_extraFive, Imp [] e.1 e.2 := apI bounds_extraFive accBounds_extraFour
end PEqualNP.Outside.L_meta_10760_first
