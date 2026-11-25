import KernelEngine
namespace PEqualNP.Outside.L_meta_10760
def candidates5 : List (Nat × Nat) := [(122, 1), (117, 1), (110, 1), (109, 1), (107, 1), (94, 1), (93, 1), (87, 1), (62, 1), (59, 1), (55, 1), (31, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert5 : candidates5.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma bounds5 : ∀ e ∈ candidates5, Imp [] e.1 e.2 := okAll cert5 (by simp)
def acc5 : List (Nat × Nat) := candidates5 ++ []
lemma accBounds5 : ∀ e ∈ acc5, Imp [] e.1 e.2 := apI bounds5 (by simp)
def candidates4 : List (Nat × Nat) := [(120, 1), (116, 1), (114, 1), (113, 1), (108, 2), (106, 4), (105, 2), (102, 1), (101, 2), (99, 1), (92, 2), (90, 2), (89, 1), (86, 2), (85, 4), (83, 1), (78, 2), (77, 2), (75, 1), (71, 1), (60, 1), (58, 4), (57, 1), (54, 2), (53, 2), (51, 2), (46, 2), (45, 1), (43, 2), (39, 1), (30, 4), (29, 2), (27, 2), (23, 4), (15, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert4 : candidates4.all (fun e => okE [] (pr acc5 e.1) e) = true := by decide +kernel
lemma bounds4 : ∀ e ∈ candidates4, Imp [] e.1 e.2 := okAll cert4 accBounds5
def acc4 : List (Nat × Nat) := candidates4 ++ acc5
lemma accBounds4 : ∀ e ∈ acc4, Imp [] e.1 e.2 := apI bounds4 accBounds5
def candidates3 : List (Nat × Nat) := [(112, 3), (104, 5), (100, 4), (98, 4), (97, 4), (88, 4), (84, 5), (82, 4), (81, 4), (76, 3), (74, 5), (73, 4), (70, 4), (69, 5), (67, 3), (56, 4), (52, 4), (50, 5), (49, 4), (44, 4), (42, 5), (41, 4), (38, 4), (37, 4), (35, 4), (28, 5), (26, 5), (25, 4), (22, 5), (21, 5), (19, 5), (14, 5), (13, 4), (11, 4), (7, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert3 : candidates3.all (fun e => okE [] (pr acc4 e.1) e) = true := by decide +kernel
lemma bounds3 : ∀ e ∈ candidates3, Imp [] e.1 e.2 := okAll cert3 accBounds4
def acc3 : List (Nat × Nat) := candidates3 ++ acc4
lemma accBounds3 : ∀ e ∈ acc3, Imp [] e.1 e.2 := apI bounds3 accBounds4
def candidates2 : List (Nat × Nat) := [(96, 7), (80, 7), (72, 6), (68, 6), (66, 7), (65, 7), (48, 7), (40, 7), (36, 7), (34, 7), (33, 7), (24, 7), (20, 7), (18, 7), (17, 7), (12, 6), (10, 7), (9, 7), (6, 7), (5, 7), (3, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert2 : candidates2.all (fun e => okE [] (pr acc3 e.1) e) = true := by decide +kernel
lemma bounds2 : ∀ e ∈ candidates2, Imp [] e.1 e.2 := okAll cert2 accBounds3
def acc2 : List (Nat × Nat) := candidates2 ++ acc3
lemma accBounds2 : ∀ e ∈ acc2, Imp [] e.1 e.2 := apI bounds2 accBounds3
def candidates1 : List (Nat × Nat) := [(64, 9), (32, 10), (16, 10), (8, 10), (4, 10), (2, 10), (1, 10)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cert1 : candidates1.all (fun e => okE [] (pr acc2 e.1) e) = true := by decide +kernel
lemma bounds1 : ∀ e ∈ candidates1, Imp [] e.1 e.2 := okAll cert1 accBounds2
def acc1 : List (Nat × Nat) := candidates1 ++ acc2
lemma accBounds1 : ∀ e ∈ acc1, Imp [] e.1 e.2 := apI bounds1 accBounds2
def marks13 : List (Nat × Nat × Nat) := [(0, FF, 1), (1, FF, 1), (2, FF, 1), (3, FF, 1), (4, FF, 1), (5, FF, 1), (6, FF, 1), (7, FF, 1), (8, FF, 1), (9, FF, 1), (10, FF, 1), (11, FF, 1), (12, FF, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma run13 : marks13.all (okS acc1 0 12) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover13 : okP acc1 0 13 marks13 = true := by decide +kernel
lemma bound13 : Imp [] 0 13 := imp_run marks13 accBounds1 cover13 run13
end PEqualNP.Outside.L_meta_10760
