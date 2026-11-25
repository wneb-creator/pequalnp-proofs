import or_first_nonor
import overlapping_or

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.OrFirstCensus

open PEqualNP.Outside.L_meta_2592_aux.Subgraphs
open PEqualNP.Outside.L_meta_1886_aux
open OrFirstNonOr

def rawOr (p q : Fin 10) : Sig := bin 1 (pins.getD p.val zero) (pins.getD q.val zero)
def triple (p : Fin 10) : Sig := bin 1 OrFirstNonOr.seed (pins.getD p.val zero)

def pairs : List (Fin 10 × Fin 10) :=
  [(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),
   (3,4),(3,5),(3,6),(3,7),(3,8),(3,9),
   (4,5),(4,6),(4,7),(4,8),(4,9),
   (5,6),(5,7),(5,8),(5,9),(6,7),(6,8),(6,9),(7,8),(7,9),(8,9),
   (0,2),(0,6),(1,4),(1,5)]
def outsiders : List (Fin 10) := [2,3,4,5,6,7,8,9]
def allowedValues : List Sig := pairs.map (fun p => rawOr p.1 p.2) ++ outsiders.map triple

def badZero : List (Fin 10) := [1,3,4,5,7,8,9]
def badOne : List (Fin 10) := [0,2,3,6,7,8,9]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma allowed_count : allowedValues.length = 40 ∧ allowedValues.Nodup := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bad_zero_checked : ∀ p ∈ badZero, adjacent 1 p = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma bad_one_checked : ∀ p ∈ badOne, adjacent 0 p = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma classification_checked : OrFirstNonOr.initial.all (fun a => OrFirstNonOr.initial.all (fun b =>
    (a == b) || (bin 1 a b == a) || (bin 1 a b == b) ||
    allowedValues.contains (bin 1 a b) ||
    badZero.any (fun p => bin 1 a b == rawOr 0 p) ||
    badOne.any (fun p => bin 1 a b == rawOr 1 p))) = true := by
  decide +kernel

lemma classified (a b : Sig) (ha : a ∈ OrFirstNonOr.initial) (hb : b ∈ OrFirstNonOr.initial)
    (hab : a ≠ b) (newA : bin 1 a b ≠ a) (newB : bin 1 a b ≠ b) :
    bin 1 a b ∈ allowedValues ∨
      (∃ p ∈ badZero, bin 1 a b = rawOr 0 p) ∨
      (∃ p ∈ badOne, bin 1 a b = rawOr 1 p) := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp classification_checked a ha) b hb
  simpa only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem,List.any_eq_true,hab,newA,newB,
    false_or,or_false,or_assoc] using h

lemma remaining (a b : Sig) (ha : a ∈ OrFirstNonOr.initial) (hb : b ∈ OrFirstNonOr.initial)
    (hab : a ≠ b) (newA : bin 1 a b ≠ a) (newB : bin 1 a b ≠ b) {S}
    (run : Live true target 15 S)
    (raw : ∀ v ∈ S, v ∈ OrFirstNonOr.bank (bin 1 a b)) : bin 1 a b ∈ allowedValues := by
  rcases classified a b ha hb hab newA newB with good | ⟨p,hp,eq⟩ | ⟨p,hp,eq⟩
  · exact good
  · have OrFirstNonOr.bank' : ∀ v ∈ S, v ∈ OverlappingOr.bank 0 p := by
      change ∀ v ∈ S, v ∈ pins ++ [OrFirstNonOr.seed,rawOr 0 p]
      simpa only [OrFirstNonOr.bank,eq] using raw
    have impossible := OverlappingOr.lower_zero p (bad_zero_checked p hp) run OrFirstNonOr.bank'
    exact ((by decide : ¬ ((16 : Nat) ≤ 15)) impossible).elim
  · have OrFirstNonOr.bank' : ∀ v ∈ S, v ∈ OverlappingOr.bank 1 p := by
      change ∀ v ∈ S, v ∈ pins ++ [OrFirstNonOr.seed,rawOr 1 p]
      simpa only [OrFirstNonOr.bank,eq] using raw
    have impossible := OverlappingOr.lower_one p (bad_one_checked p hp) run OrFirstNonOr.bank'
    exact ((by decide : ¬ ((16 : Nat) ≤ 15)) impossible).elim

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_or_census {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ OrFirstNonOr.initial) (budget : k ≤ 16) :
    k = 16 ∧ ∃ (v : Sig) (T : Finset Sig), v ∈ allowedValues ∧
      Live true target 15 T ∧ v ∈ T ∧ ∀ a ∈ T, a ∈ OrFirstNonOr.bank v := by
  obtain ⟨hk,a,b,T,ha,hb,hab,newA,newB,tail,used,rawTail⟩ := first_or_of_sixteen run raw budget
  exact ⟨hk,bin 1 a b,T,remaining a b ha hb hab newA newB tail rawTail,tail,used,rawTail⟩

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.OrFirstCensus
