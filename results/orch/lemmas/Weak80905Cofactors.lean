import Weak80905Profiles
import Weak80905Data
import RunCofactorCheck

namespace PEqualNP.Outside.L_meta_2373.Weak80905

open Live1024

def terminalWs76617 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76617 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76617 : runCofactorCheck false inputs (Mono18Profiles.domain10) 11 14 terminalWs76617 terminalChoices76617 = true := by
  decide +kernel
theorem terminalRun76617 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76617.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice10 terminalCheck76617 bound

def terminalWs76618 : List Sig := [s1, s2, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76618 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76618 : runCofactorCheck false inputs (Mono18Profiles.domain11) 11 14 terminalWs76618 terminalChoices76618 = true := by
  decide +kernel
theorem terminalRun76618 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76618.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice11 terminalCheck76618 bound

def terminalWs76619 : List Sig := [s1, s2, s3, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76619 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76619 : runCofactorCheck false inputs (Mono18Profiles.domain2) 15 14 terminalWs76619 terminalChoices76619 = true := by
  decide +kernel
theorem terminalRun76619 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76619.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice2 terminalCheck76619 bound

def terminalWs76620 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76620 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76620 : runCofactorCheck false inputs (Mono18Profiles.domain3) 15 14 terminalWs76620 terminalChoices76620 = true := by
  decide +kernel
theorem terminalRun76620 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76620.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice3 terminalCheck76620 bound

def terminalWs76621 : List Sig := [s1, s2, s3, s4, s5, s5, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76621 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76621 : runCofactorCheck false inputs (Mono18Profiles.domain74) 10 14 terminalWs76621 terminalChoices76621 = true := by
  decide +kernel
theorem terminalRun76621 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76621.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice74 terminalCheck76621 bound

def terminalWs76622 : List Sig := [s1, s2, s3, s4, s5, s6, s6, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76622 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76622 : runCofactorCheck false inputs (Mono18Profiles.domain76) 10 14 terminalWs76622 terminalChoices76622 = true := by
  decide +kernel
theorem terminalRun76622 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76622.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice76 terminalCheck76622 bound

def terminalWs76623 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s7, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76623 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76623 : runCofactorCheck false inputs (Mono18Profiles.domain16) 11 14 terminalWs76623 terminalChoices76623 = true := by
  decide +kernel
theorem terminalRun76623 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76623.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice16 terminalCheck76623 bound

def terminalWs76624 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s8, s8, s9, s10, s13864, s13864]
def terminalChoices76624 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76624 : runCofactorCheck false inputs (Mono18Profiles.domain41) 13 14 terminalWs76624 terminalChoices76624 = true := by
  decide +kernel
theorem terminalRun76624 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76624.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice41 terminalCheck76624 bound

def terminalWs76625 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s9, s10, s13864, s13864]
def terminalChoices76625 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76625 : runCofactorCheck false inputs (Mono18Profiles.domain174) 10 14 terminalWs76625 terminalChoices76625 = true := by
  decide +kernel
theorem terminalRun76625 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76625.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice174 terminalCheck76625 bound

def terminalWs76626 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s10, s13864, s13864]
def terminalChoices76626 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76626 : runCofactorCheck false inputs (Mono18Profiles.domain176) 10 14 terminalWs76626 terminalChoices76626 = true := by
  decide +kernel
theorem terminalRun76626 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76626.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice176 terminalCheck76626 bound

def terminalWs76627 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s8, s9, s10, s13864, s13864, s13864]
def terminalChoices76627 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck76627 : runCofactorCheck false inputs (Mono18Profiles.domain10) 11 14 terminalWs76627 terminalChoices76627 = true := by
  decide +kernel
theorem terminalRun76627 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs76627.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice10 terminalCheck76627 bound

def terminalWs80906 : List Sig := [s1, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80906 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80906 : runCofactorCheck false inputs (Mono18Profiles.domain10) 11 14 terminalWs80906 terminalChoices80906 = true := by
  decide +kernel
theorem terminalRun80906 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80906.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice10 terminalCheck80906 bound

def terminalWs80907 : List Sig := [s1, s2, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80907 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80907 : runCofactorCheck false inputs (Mono18Profiles.domain11) 11 14 terminalWs80907 terminalChoices80907 = true := by
  decide +kernel
theorem terminalRun80907 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80907.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice11 terminalCheck80907 bound

def terminalWs80908 : List Sig := [s1, s2, s3, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80908 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80908 : runCofactorCheck false inputs (Mono18Profiles.domain2) 15 14 terminalWs80908 terminalChoices80908 = true := by
  decide +kernel
theorem terminalRun80908 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80908.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice2 terminalCheck80908 bound

def terminalWs80909 : List Sig := [s1, s2, s3, s4, s4, s5, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80909 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80909 : runCofactorCheck false inputs (Mono18Profiles.domain3) 15 14 terminalWs80909 terminalChoices80909 = true := by
  decide +kernel
theorem terminalRun80909 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80909.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice3 terminalCheck80909 bound

def terminalWs80910 : List Sig := [s1, s2, s3, s4, s5, s5, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80910 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80910 : runCofactorCheck false inputs (Mono18Profiles.domain74) 10 14 terminalWs80910 terminalChoices80910 = true := by
  decide +kernel
theorem terminalRun80910 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80910.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice74 terminalCheck80910 bound

def terminalWs80911 : List Sig := [s1, s2, s3, s4, s5, s6, s6, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80911 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80911 : runCofactorCheck false inputs (Mono18Profiles.domain76) 10 14 terminalWs80911 terminalChoices80911 = true := by
  decide +kernel
theorem terminalRun80911 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80911.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice76 terminalCheck80911 bound

def terminalWs80912 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s7, s8, s9, s10, s13864, s13864]
def terminalChoices80912 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80912 : runCofactorCheck false inputs (Mono18Profiles.domain16) 11 14 terminalWs80912 terminalChoices80912 = true := by
  decide +kernel
theorem terminalRun80912 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80912.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice16 terminalCheck80912 bound

def terminalWs80914 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s9, s10, s13864, s13864]
def terminalChoices80914 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80914 : runCofactorCheck false inputs (Mono18Profiles.domain174) 10 14 terminalWs80914 terminalChoices80914 = true := by
  decide +kernel
theorem terminalRun80914 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80914.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice174 terminalCheck80914 bound

def terminalWs80915 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s10, s13864, s13864]
def terminalChoices80915 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80915 : runCofactorCheck false inputs (Mono18Profiles.domain176) 10 14 terminalWs80915 terminalChoices80915 = true := by
  decide +kernel
theorem terminalRun80915 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80915.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice176 terminalCheck80915 bound

def terminalWs80916 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s13864, s13864]
def terminalChoices80916 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem terminalCheck80916 : runCofactorCheck false inputs (Mono18Profiles.domain10) 11 14 terminalWs80916 terminalChoices80916 = true := by
  decide +kernel
theorem terminalRun80916 {k : Nat} (bound : k ≤ 14) :
    ¬ Run false (observe graph) k (terminalWs80916.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice10 terminalCheck80916 bound

def gateWs0 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s29951]
def gateChoices0 : List Choice := [(1, s1, s2), (1, s7, s12)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gateCheck0 : runCofactorCheck false inputs (Mono18Profiles.domain41) 13 13 gateWs0 gateChoices0 = true := by
  decide +kernel
theorem gateRun0 {k : Nat} (bound : k ≤ 13) :
    ¬ Run false (observe graph) k (gateWs0.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice41 gateCheck0 bound

def gateWs1 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864, s15934]
def gateChoices1 : List Choice := []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gateCheck1 : runCofactorCheck false inputs (Mono18Profiles.domain10) 11 13 gateWs1 gateChoices1 = true := by
  decide +kernel
theorem gateRun1 {k : Nat} (bound : k ≤ 13) :
    ¬ Run false (observe graph) k (gateWs1.map observe) :=
  runCofactorCheck_sound Mono18Profiles.slice10 gateCheck1 bound

end PEqualNP.Outside.L_meta_2373.Weak80905
