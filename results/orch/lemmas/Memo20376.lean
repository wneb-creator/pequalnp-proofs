import CofactorMoves
import CountVectorRegroup

namespace PEqualNP.Outside.L_meta_2373.Memo20376
open Live1024 Live1024.CofactorMoves CountVector

def swap (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  (a &&& ~~~b, b &&& ~~~a, Fin.ofNat 1024 ((1 <<< j) - (1 <<< i)))

def moves : List Move := [swap 98, swap 131, swap 84, swap 151]
def rows : Row → Row := movedRow moves

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma rows_inverse : ∀ r : Row, rows (rows r) = r := by decide +kernel

lemma rows_onto : Function.Surjective rows := fun r => ⟨rows r, rows_inverse r⟩

lemma target_word : movedWord moves graph = graph := by decide +kernel
lemma target_fixed : rename rows graph = graph := by
  exact (moved_eq_rename moves graph).symm.trans target_word

def s1477 : Sig := 0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def s1761 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000
def s6015 : Sig := 0xffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s7093 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

def sourceSignal : Fin 11 → Sig := ![(inputs.getD 0 zero), (inputs.getD 1 zero), (inputs.getD 2 zero), (inputs.getD 3 zero), (inputs.getD 4 zero), (inputs.getD 5 zero), (inputs.getD 6 zero), (inputs.getD 8 zero), (inputs.getD 9 zero), s1477, s6015]
def priorSignal : Fin 11 → Sig := ![(inputs.getD 0 zero), (inputs.getD 1 zero), (inputs.getD 2 zero), (inputs.getD 3 zero), (inputs.getD 4 zero), (inputs.getD 5 zero), (inputs.getD 6 zero), (inputs.getD 7 zero), (inputs.getD 8 zero), s1761, s7093]
def classMap : Fin 11 → Fin 11 := ![0, 1, 6, 8, 5, 4, 2, 3, 7, 9, 10]
def sourceTotal : Fin 11 → Nat := ![2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2]
def priorTotal : Fin 11 → Nat := ![2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2]

lemma signals_word : ∀ j : Fin 11, priorSignal (classMap j) = movedWord moves (sourceSignal j) := by
  decide +kernel

lemma signals : ∀ j : Fin 11, priorSignal (classMap j) = rename rows (sourceSignal j) := by
  intro j
  exact (signals_word j).trans (moved_eq_rename moves _)

lemma totals : regroup classMap sourceTotal = priorTotal := by
  funext j; fin_cases j <;> decide +kernel

end PEqualNP.Outside.L_meta_2373.Memo20376
