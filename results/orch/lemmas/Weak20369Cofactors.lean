import Mono18FullProfiles
import Weak20369Data
import RunCofactorCheck

namespace PEqualNP.Outside.L_meta_2373.Weak20369

open Live1024

def terminalWs20370 : List Sig := [s1, s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20370 : List Choice := [(0, s4, s9), (1, s8, s565), (1, s12, s1477)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20370 : runCofactorCheck false inputs (Mono18FullProfiles.domain 0)
    (Mono18FullProfiles.bound 0) 14 terminalWs20370 terminalChoices20370 = true := by
  decide +kernel
theorem terminalRun20370 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20370.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 0) terminalCheck20370 bound

def terminalWs20371 : List Sig := [s1, s1, s2, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20371 : List Choice := [(0, s4, s9), (1, s8, s565)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20371 : runCofactorCheck false inputs (Mono18FullProfiles.domain 20)
    (Mono18FullProfiles.bound 20) 14 terminalWs20371 terminalChoices20371 = true := by
  decide +kernel
theorem terminalRun20371 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20371.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 20) terminalCheck20371 bound

def terminalWs20372 : List Sig := [s1, s1, s2, s3, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20372 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20372 : runCofactorCheck false inputs (Mono18FullProfiles.domain 122)
    (Mono18FullProfiles.bound 122) 14 terminalWs20372 terminalChoices20372 = true := by
  decide +kernel
theorem terminalRun20372 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20372.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 122) terminalCheck20372 bound

def terminalWs20373 : List Sig := [s1, s1, s2, s3, s4, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20373 : List Choice := [(1, s1, s2), (1, s12, s1477)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20373 : runCofactorCheck false inputs (Mono18FullProfiles.domain 3)
    (Mono18FullProfiles.bound 3) 14 terminalWs20373 terminalChoices20373 = true := by
  decide +kernel
theorem terminalRun20373 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20373.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 3) terminalCheck20373 bound

def terminalWs20374 : List Sig := [s1, s1, s2, s3, s4, s5, s5, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20374 : List Choice := [(1, s12, s1477)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20374 : runCofactorCheck false inputs (Mono18FullProfiles.domain 200)
    (Mono18FullProfiles.bound 200) 14 terminalWs20374 terminalChoices20374 = true := by
  decide +kernel
theorem terminalRun20374 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20374.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 200) terminalCheck20374 bound

def terminalWs20375 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s6, s7, s9, s10, s1477, s6015, s6015]
def terminalChoices20375 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20375 : runCofactorCheck false inputs (Mono18FullProfiles.domain 163)
    (Mono18FullProfiles.bound 163) 14 terminalWs20375 terminalChoices20375 = true := by
  decide +kernel
theorem terminalRun20375 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20375.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 163) terminalCheck20375 bound

def terminalWs20377 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s9, s9, s10, s1477, s6015, s6015]
def terminalChoices20377 : List Choice := [(1, s1, s2), (1, s12, s1477)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20377 : runCofactorCheck false inputs (Mono18FullProfiles.domain 8)
    (Mono18FullProfiles.bound 8) 14 terminalWs20377 terminalChoices20377 = true := by
  decide +kernel
theorem terminalRun20377 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20377.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 8) terminalCheck20377 bound

def terminalWs20378 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s10, s1477, s6015, s6015]
def terminalChoices20378 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20378 : runCofactorCheck false inputs (Mono18FullProfiles.domain 181)
    (Mono18FullProfiles.bound 181) 14 terminalWs20378 terminalChoices20378 = true := by
  decide +kernel
theorem terminalRun20378 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20378.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 181) terminalCheck20378 bound

def terminalWs20379 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s1477, s6015, s6015]
def terminalChoices20379 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20379 : runCofactorCheck false inputs (Mono18FullProfiles.domain 17)
    (Mono18FullProfiles.bound 17) 14 terminalWs20379 terminalChoices20379 = true := by
  decide +kernel
theorem terminalRun20379 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20379.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 17) terminalCheck20379 bound

def terminalWs20380 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s9, s10, s1477, s6015, s6015, s6015]
def terminalChoices20380 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem terminalCheck20380 : runCofactorCheck false inputs (Mono18FullProfiles.domain 17)
    (Mono18FullProfiles.bound 17) 14 terminalWs20380 terminalChoices20380 = true := by
  decide +kernel
theorem terminalRun20380 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs20380.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 17) terminalCheck20380 bound

def gateWs0 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7093, s27]
def gateChoices0 : List Choice := [(0, s4, s9), (1, s10, s565), (1, s12, s1761)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gateCheck0 : runCofactorCheck false inputs (Mono18FullProfiles.domain 0)
    (Mono18FullProfiles.bound 0) 13 gateWs0 gateChoices0 = true := by
  decide +kernel
theorem gateRun0 {k : Nat} (bound : k ≤ 13) :
    ¬ Run false (observe graph) k (gateWs0.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 0) gateCheck0 bound

def gateWs1 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s8377]
def gateChoices1 : List Choice := [(1, s1, s2), (1, s12, s1761)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gateCheck1 : runCofactorCheck false inputs (Mono18FullProfiles.domain 37)
    (Mono18FullProfiles.bound 37) 13 gateWs1 gateChoices1 = true := by
  decide +kernel
theorem gateRun1 {k : Nat} (bound : k ≤ 13) :
    ¬ Run false (observe graph) k (gateWs1.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 37) gateCheck1 bound

def gateWs2 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7321]
def gateChoices2 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gateCheck2 : runCofactorCheck false inputs (Mono18FullProfiles.domain 19)
    (Mono18FullProfiles.bound 19) 13 gateWs2 gateChoices2 = true := by
  decide +kernel
theorem gateRun2 {k : Nat} (bound : k ≤ 13) :
    ¬ Run false (observe graph) k (gateWs2.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 19) gateCheck2 bound

def gateWs3 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s8379]
def gateChoices3 : List Choice := [(1, s1, s2), (1, s12, s1761)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gateCheck3 : runCofactorCheck false inputs (Mono18FullProfiles.domain 37)
    (Mono18FullProfiles.bound 37) 12 gateWs3 gateChoices3 = true := by
  decide +kernel
theorem gateRun3 {k : Nat} (bound : k ≤ 12) :
    ¬ Run false (observe graph) k (gateWs3.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 37) gateCheck3 bound

def gateWs4 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s1761, s7093, s7321]
def gateChoices4 : List Choice := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem gateCheck4 : runCofactorCheck false inputs (Mono18FullProfiles.domain 19)
    (Mono18FullProfiles.bound 19) 12 gateWs4 gateChoices4 = true := by
  decide +kernel
theorem gateRun4 {k : Nat} (bound : k ≤ 12) :
    ¬ Run false (observe graph) k (gateWs4.map observe) :=
  runCofactorCheck_sound (Mono18FullProfiles.slice 19) gateCheck4 bound

end PEqualNP.Outside.L_meta_2373.Weak20369
