import Node1098Profiles
import CountFixture1098
import RunCofactorCheck

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098

open Live1024

def cutWs0 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1514, s38]
def cutChoices0 : List Choice := [(1, s7, s15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck0 : runCofactorCheck false inputs (Node1098Profiles.domain 3) 13 15 cutWs0 cutChoices0 = true := by
  decide +kernel
theorem cutRun0 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs0.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 3) cutCheck0 bound

def cutWs1 : List Sig := [s1, s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1514, s43]
def cutChoices1 : List Choice := [(1, s2, s3), (1, s7, s15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck1 : runCofactorCheck false inputs (Node1098Profiles.domain 1) 15 15 cutWs1 cutChoices1 = true := by
  decide +kernel
theorem cutRun1 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs1.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 1) cutCheck1 bound

def cutWs2 : List Sig := [s1, s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1514, s44]
def cutChoices2 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck2 : runCofactorCheck false inputs (Node1098Profiles.domain 4) 10 15 cutWs2 cutChoices2 = true := by
  decide +kernel
theorem cutRun2 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs2.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 4) cutCheck2 bound

def cutWs3 : List Sig := [s1, s2, s3, s4, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1672]
def cutChoices3 : List Choice := [(1, s7, s15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck3 : runCofactorCheck false inputs (Node1098Profiles.domain 3) 13 15 cutWs3 cutChoices3 = true := by
  decide +kernel
theorem cutRun3 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs3.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 3) cutCheck3 bound

def cutWs4 : List Sig := [s1, s2, s3, s4, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1536]
def cutChoices4 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck4 : runCofactorCheck false inputs (Node1098Profiles.domain 8) 9 15 cutWs4 cutChoices4 = true := by
  decide +kernel
theorem cutRun4 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs4.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 8) cutCheck4 bound

def cutWs5 : List Sig := [s1, s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1673]
def cutChoices5 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck5 : runCofactorCheck false inputs (Node1098Profiles.domain 6) 11 15 cutWs5 cutChoices5 = true := by
  decide +kernel
theorem cutRun5 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs5.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 6) cutCheck5 bound

def cutWs6 : List Sig := [s1, s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1557]
def cutChoices6 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck6 : runCofactorCheck false inputs (Node1098Profiles.domain 4) 10 15 cutWs6 cutChoices6 = true := by
  decide +kernel
theorem cutRun6 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs6.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 4) cutCheck6 bound

def cutWs7 : List Sig := [s1, s1, s2, s3, s4, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1675]
def cutChoices7 : List Choice := [(1, s7, s15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck7 : runCofactorCheck false inputs (Node1098Profiles.domain 3) 13 15 cutWs7 cutChoices7 = true := by
  decide +kernel
theorem cutRun7 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs7.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 3) cutCheck7 bound

def cutWs8 : List Sig := [s1, s1, s2, s3, s4, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1536]
def cutChoices8 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck8 : runCofactorCheck false inputs (Node1098Profiles.domain 5) 10 15 cutWs8 cutChoices8 = true := by
  decide +kernel
theorem cutRun8 {k : Nat} (bound : k ≤ 15) :
    ¬ Run false (observe graph) k (cutWs8.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 5) cutCheck8 bound

def cutWs9 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1514, s51]
def cutChoices9 : List Choice := [(1, s7, s15)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck9 : runCofactorCheck false inputs (Node1098Profiles.domain 0) 15 14 cutWs9 cutChoices9 = true := by
  decide +kernel
theorem cutRun9 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (cutWs9.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 0) cutCheck9 bound

def cutWs10 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s1514, s1514, s44]
def cutChoices10 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck10 : runCofactorCheck false inputs (Node1098Profiles.domain 2) 11 14 cutWs10 cutChoices10 = true := by
  decide +kernel
theorem cutRun10 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (cutWs10.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 2) cutCheck10 bound

def cutWs11 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1676]
def cutChoices11 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck11 : runCofactorCheck false inputs (Node1098Profiles.domain 7) 11 14 cutWs11 cutChoices11 = true := by
  decide +kernel
theorem cutRun11 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (cutWs11.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 7) cutCheck11 bound

def cutWs12 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s12, s1514, s1609]
def cutChoices12 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutCheck12 : runCofactorCheck false inputs (Node1098Profiles.domain 2) 11 14 cutWs12 cutChoices12 = true := by
  decide +kernel
theorem cutRun12 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (cutWs12.map observe) :=
  runCofactorCheck_sound (Node1098Profiles.slice 2) cutCheck12 bound

end PEqualNP.Outside.L_meta_2373.CountFixture1098
