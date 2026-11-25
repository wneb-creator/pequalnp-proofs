import SliceProfiles
import RunCofactorCheck

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

def s0 : Sig := inputs.getD 0 zero
def s1 : Sig := inputs.getD 1 zero
def s2 : Sig := inputs.getD 2 zero
def s3 : Sig := inputs.getD 3 zero
def s4 : Sig := inputs.getD 4 zero
def s5 : Sig := inputs.getD 5 zero
def s6 : Sig := inputs.getD 6 zero
def s7 : Sig := inputs.getD 7 zero
def s8 : Sig := inputs.getD 8 zero
def s9 : Sig := inputs.getD 9 zero
def s10 : Sig := bin 0 s0 s1
def s11 : Sig := bin 1 s10 s2
def s12 : Sig := bin 0 s11 s3
def s13 : Sig := bin 1 s0 s12
def s14 : Sig := bin 1 s13 s5
def s15 : Sig := bin 1 s13 s7
def s16 : Sig := bin 1 s6 s8
def s17 : Sig := graph
def s18 : Sig := bin 0 s14 s15
def s19 : Sig := bin 1 s5 s1
def s20 : Sig := bin 1 s7 s1
def s21 : Sig := bin 1 s8 s1
def s22 : Sig := bin 0 s16 s1
def s23 : Sig := bin 1 s16 s1
def s24 : Sig := bin 0 s16 s21
def s25 : Sig := bin 1 s14 s11
def s26 : Sig := bin 0 s16 s11
def s27 : Sig := bin 1 s16 s11
def s28 : Sig := bin 0 s15 s25
def s29 : Sig := bin 1 s14 s26
def s30 : Sig := bin 0 s1 s27
def s31 : Sig := bin 1 s14 s3
def s32 : Sig := bin 1 s6 s3
def s33 : Sig := bin 0 s16 s3
def s34 : Sig := bin 1 s16 s3
def s35 : Sig := bin 0 s15 s31
def s36 : Sig := bin 0 s16 s32
def s37 : Sig := bin 1 s5 s4
def s38 : Sig := bin 0 s14 s4
def s39 : Sig := bin 1 s7 s4
def s40 : Sig := bin 0 s16 s4
def s41 : Sig := bin 1 s16 s4
def s42 : Sig := bin 0 s14 s37
def s43 : Sig := bin 1 s5 s40
def s44 : Sig := bin 1 s7 s40
def s45 : Sig := bin 0 s14 s41
def s46 : Sig := bin 1 s6 s5
def s47 : Sig := bin 1 s7 s5
def s48 : Sig := bin 0 s16 s5
def s49 : Sig := bin 1 s16 s5
def s50 : Sig := bin 0 s16 s46
def s51 : Sig := bin 0 s16 s14
def s52 : Sig := bin 1 s16 s14
def s53 : Sig := bin 0 s15 s52
def s54 : Sig := bin 0 s16 s7
def s55 : Sig := bin 1 s16 s7
def s56 : Sig := bin 0 s16 s15
def s57 : Sig := bin 1 s16 s15
def s58 : Sig := bin 0 s5 s57
def s59 : Sig := bin 0 s14 s57
def s60 : Sig := bin 1 s15 s8
def s61 : Sig := bin 0 s14 s60
def s62 : Sig := bin 1 s14 s9
def s63 : Sig := bin 1 s8 s9
def s64 : Sig := bin 0 s16 s9
def s65 : Sig := bin 1 s16 s9
def s66 : Sig := bin 0 s15 s62
def s67 : Sig := bin 0 s16 s63
def s68 : Sig := bin 1 s14 s64
def s69 : Sig := bin 1 s15 s64
def s70 : Sig := bin 1 s18 s64
def s71 : Sig := bin 0 s15 s68
def s72 : Sig := bin 0 s14 s69
def s73 : Sig := bin 0 s16 s18
def s74 : Sig := bin 1 s16 s18

def cutWs0 : List Sig := [s1, s11, s3, s4, s6, s7, s8, s16, s9, s5, s5, s18]
def cutChoices0 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck0 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 11 cutWs0 cutChoices0 = true := by
  decide +kernel
theorem cutRun0 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs0.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck0 bound

def cutWs1 : List Sig := [s1, s11, s3, s4, s5, s6, s8, s16, s9, s7, s7, s18]
def cutChoices1 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck1 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 11 cutWs1 cutChoices1 = true := by
  decide +kernel
theorem cutRun1 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs1.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck1 bound

def cutWs2 : List Sig := [s11, s3, s4, s5, s14, s6, s7, s15, s8, s9, s1, s22]
def cutChoices2 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck2 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 11 cutWs2 cutChoices2 = true := by
  decide +kernel
theorem cutRun2 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs2.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck2 bound

def cutWs3 : List Sig := [s11, s3, s4, s5, s14, s6, s7, s15, s8, s9, s1, s22]
def cutChoices3 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck3 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 11 cutWs3 cutChoices3 = true := by
  decide +kernel
theorem cutRun3 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs3.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck3 bound

def cutWs4 : List Sig := [s11, s3, s4, s5, s14, s6, s7, s15, s9, s1, s24]
def cutChoices4 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck4 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 10 cutWs4 cutChoices4 = true := by
  decide +kernel
theorem cutRun4 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs4.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck4 bound

def cutWs5 : List Sig := [s11, s3, s4, s5, s14, s6, s7, s15, s9, s1, s24]
def cutChoices5 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck5 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 10 cutWs5 cutChoices5 = true := by
  decide +kernel
theorem cutRun5 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs5.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck5 bound

def cutWs6 : List Sig := [s1, s3, s4, s5, s6, s7, s8, s16, s9, s11, s28]
def cutChoices6 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck6 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs6 cutChoices6 = true := by
  decide +kernel
theorem cutRun6 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs6.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck6 bound

def cutWs7 : List Sig := [s1, s3, s4, s5, s6, s7, s15, s8, s9, s11, s29]
def cutChoices7 : List Choice := [(0, s0, s1), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck7 : runCofactorCheck false inputs (ZeroProfiles.domain 2) 15 10 cutWs7 cutChoices7 = true := by
  decide +kernel
theorem cutRun7 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs7.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 2) cutCheck7 bound

def cutWs8 : List Sig := [s3, s4, s5, s14, s6, s7, s15, s8, s9, s11, s30]
def cutChoices8 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck8 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 10 cutWs8 cutChoices8 = true := by
  decide +kernel
theorem cutRun8 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs8.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck8 bound

def cutWs9 : List Sig := [s1, s3, s4, s5, s6, s7, s8, s16, s9, s11, s28]
def cutChoices9 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck9 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs9 cutChoices9 = true := by
  decide +kernel
theorem cutRun9 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs9.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck9 bound

def cutWs10 : List Sig := [s1, s3, s4, s5, s6, s7, s15, s8, s9, s11, s29]
def cutChoices10 : List Choice := [(0, s0, s1), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck10 : runCofactorCheck false inputs (ZeroProfiles.domain 2) 15 10 cutWs10 cutChoices10 = true := by
  decide +kernel
theorem cutRun10 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs10.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 2) cutCheck10 bound

def cutWs11 : List Sig := [s3, s4, s5, s14, s6, s7, s15, s8, s9, s11, s30]
def cutChoices11 : List Choice := [(0, s11, s3), (1, s0, s12), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck11 : runCofactorCheck false inputs (ZeroProfiles.domain 1) 15 10 cutWs11 cutChoices11 = true := by
  decide +kernel
theorem cutRun11 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs11.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 1) cutCheck11 bound

def cutWs12 : List Sig := [s1, s11, s4, s5, s14, s6, s7, s15, s8, s9, s3, s33]
def cutChoices12 : List Choice := [(0, s0, s1), (1, s10, s2), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck12 : runCofactorCheck false inputs (ZeroProfiles.domain 3) 15 11 cutWs12 cutChoices12 = true := by
  decide +kernel
theorem cutRun12 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs12.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 3) cutCheck12 bound

def cutWs13 : List Sig := [s1, s11, s4, s5, s14, s6, s7, s15, s8, s9, s3, s33]
def cutChoices13 : List Choice := [(0, s0, s1), (1, s10, s2), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck13 : runCofactorCheck false inputs (ZeroProfiles.domain 3) 15 11 cutWs13 cutChoices13 = true := by
  decide +kernel
theorem cutRun13 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs13.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 3) cutCheck13 bound

def cutWs14 : List Sig := [s1, s11, s4, s5, s6, s7, s8, s16, s9, s3, s35]
def cutChoices14 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck14 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs14 cutChoices14 = true := by
  decide +kernel
theorem cutRun14 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs14.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck14 bound

def cutWs15 : List Sig := [s1, s11, s4, s5, s14, s7, s15, s8, s9, s3, s36]
def cutChoices15 : List Choice := [(0, s0, s1), (1, s10, s2), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck15 : runCofactorCheck false inputs (ZeroProfiles.domain 3) 15 10 cutWs15 cutChoices15 = true := by
  decide +kernel
theorem cutRun15 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs15.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 3) cutCheck15 bound

def cutWs16 : List Sig := [s1, s11, s4, s5, s6, s7, s8, s16, s9, s3, s35]
def cutChoices16 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck16 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs16 cutChoices16 = true := by
  decide +kernel
theorem cutRun16 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs16.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck16 bound

def cutWs17 : List Sig := [s1, s11, s4, s5, s14, s7, s15, s8, s9, s3, s36]
def cutChoices17 : List Choice := [(0, s0, s1), (1, s10, s2), (1, s13, s5), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck17 : runCofactorCheck false inputs (ZeroProfiles.domain 3) 15 10 cutWs17 cutChoices17 = true := by
  decide +kernel
theorem cutRun17 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs17.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 3) cutCheck17 bound

def cutWs18 : List Sig := [s1, s11, s3, s4, s6, s7, s8, s16, s9, s5, s5, s18]
def cutChoices18 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck18 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 11 cutWs18 cutChoices18 = true := by
  decide +kernel
theorem cutRun18 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs18.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck18 bound

def cutWs19 : List Sig := [s1, s11, s3, s4, s14, s6, s7, s15, s8, s9, s5, s48]
def cutChoices19 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck19 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 11 cutWs19 cutChoices19 = true := by
  decide +kernel
theorem cutRun19 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs19.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck19 bound

def cutWs20 : List Sig := [s1, s11, s3, s4, s14, s6, s7, s15, s8, s9, s5, s48]
def cutChoices20 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck20 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 11 cutWs20 cutChoices20 = true := by
  decide +kernel
theorem cutRun20 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs20.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck20 bound

def cutWs21 : List Sig := [s1, s11, s3, s4, s14, s7, s15, s8, s9, s5, s50]
def cutChoices21 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck21 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs21 cutChoices21 = true := by
  decide +kernel
theorem cutRun21 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs21.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck21 bound

def cutWs22 : List Sig := [s1, s11, s3, s4, s14, s7, s15, s8, s9, s5, s50]
def cutChoices22 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck22 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs22 cutChoices22 = true := by
  decide +kernel
theorem cutRun22 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs22.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck22 bound

def cutWs23 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s14, s53]
def cutChoices23 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s5)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck23 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs23 cutChoices23 = true := by
  decide +kernel
theorem cutRun23 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs23.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck23 bound

def cutWs24 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s14, s53]
def cutChoices24 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s5)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck24 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs24 cutChoices24 = true := by
  decide +kernel
theorem cutRun24 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs24.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck24 bound

def cutWs25 : List Sig := [s1, s11, s3, s4, s5, s6, s8, s16, s9, s7, s7, s18]
def cutChoices25 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck25 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 11 cutWs25 cutChoices25 = true := by
  decide +kernel
theorem cutRun25 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs25.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck25 bound

def cutWs26 : List Sig := [s1, s11, s3, s4, s5, s14, s6, s15, s8, s9, s7, s54]
def cutChoices26 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s5)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck26 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 11 cutWs26 cutChoices26 = true := by
  decide +kernel
theorem cutRun26 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs26.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck26 bound

def cutWs27 : List Sig := [s1, s11, s3, s4, s5, s14, s6, s15, s8, s9, s7, s54]
def cutChoices27 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s5)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck27 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 11 cutWs27 cutChoices27 = true := by
  decide +kernel
theorem cutRun27 {k : Nat} (bound : k ≤ 11) :
    ¬ Run false (observe graph) k (cutWs27.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck27 bound

def cutWs28 : List Sig := [s1, s11, s3, s4, s14, s6, s7, s8, s9, s15, s58]
def cutChoices28 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck28 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs28 cutChoices28 = true := by
  decide +kernel
theorem cutRun28 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs28.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck28 bound

def cutWs29 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s15, s59]
def cutChoices29 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck29 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs29 cutChoices29 = true := by
  decide +kernel
theorem cutRun29 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs29.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck29 bound

def cutWs30 : List Sig := [s1, s11, s3, s4, s14, s6, s7, s8, s9, s15, s58]
def cutChoices30 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck30 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs30 cutChoices30 = true := by
  decide +kernel
theorem cutRun30 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs30.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck30 bound

def cutWs31 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s15, s59]
def cutChoices31 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s13, s7)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck31 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs31 cutChoices31 = true := by
  decide +kernel
theorem cutRun31 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs31.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck31 bound

def cutWs32 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s16, s9, s8, s61]
def cutChoices32 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck32 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs32 cutChoices32 = true := by
  decide +kernel
theorem cutRun32 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs32.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck32 bound

def cutWs33 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s16, s9, s8, s61]
def cutChoices33 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck33 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 10 cutWs33 cutChoices33 = true := by
  decide +kernel
theorem cutRun33 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs33.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck33 bound

def cutWs34 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s16, s9, s66]
def cutChoices34 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck34 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs34 cutChoices34 = true := by
  decide +kernel
theorem cutRun34 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs34.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck34 bound

def cutWs35 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s16, s9, s66]
def cutChoices35 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12), (1, s6, s8)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck35 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 10 cutWs35 cutChoices35 = true := by
  decide +kernel
theorem cutRun35 {k : Nat} (bound : k ≤ 10) :
    ¬ Run false (observe graph) k (cutWs35.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck35 bound

def cutWs36 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s71]
def cutChoices36 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck36 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 9 cutWs36 cutChoices36 = true := by
  decide +kernel
theorem cutRun36 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs36.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck36 bound

def cutWs37 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s72]
def cutChoices37 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck37 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 9 cutWs37 cutChoices37 = true := by
  decide +kernel
theorem cutRun37 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs37.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck37 bound

def cutWs38 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s71]
def cutChoices38 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck38 : runCofactorCheck false inputs (ZeroProfiles.domain 7) 15 9 cutWs38 cutChoices38 = true := by
  decide +kernel
theorem cutRun38 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs38.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 7) cutCheck38 bound

def cutWs39 : List Sig := [s1, s11, s3, s4, s5, s6, s7, s8, s9, s72]
def cutChoices39 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck39 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 9 cutWs39 cutChoices39 = true := by
  decide +kernel
theorem cutRun39 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs39.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck39 bound

def cutWs40 : List Sig := [s1, s11, s3, s4, s6, s7, s8, s9, s18, s58]
def cutChoices40 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck40 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 9 cutWs40 cutChoices40 = true := by
  decide +kernel
theorem cutRun40 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs40.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck40 bound

def cutWs41 : List Sig := [s1, s11, s3, s4, s6, s7, s8, s9, s18, s58]
def cutChoices41 : List Choice := [(0, s0, s1), (1, s10, s2), (0, s11, s3), (1, s0, s12)]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cutCheck41 : runCofactorCheck false inputs (ZeroProfiles.domain 5) 15 9 cutWs41 cutChoices41 = true := by
  decide +kernel
theorem cutRun41 {k : Nat} (bound : k ≤ 9) :
    ¬ Run false (observe graph) k (cutWs41.map observe) :=
  runCofactorCheck_sound (ZeroProfiles.slice 5) cutCheck41 bound

end PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0
