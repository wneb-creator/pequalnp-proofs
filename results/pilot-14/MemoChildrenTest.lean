import DynamicBase
namespace PEqualNP.Outside.L_meta_670_aux.MemoChildren

open LiveCheck

inductive Move where
  | unary (a : Sig)
  | binary (isOr : Bool) (a b : Sig)

def Move.value : Move → Sig
  | .unary a => neg a
  | .binary d a b => bin d a b

structure Proposal where
  nots : Nat
  wires : List Sig
  move : Move

def gateLists (k t : Nat) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : List (List Sig) :=
  if !(gateAvailable v g) then [] else
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    if base == top then [g::rest] else []
  else keep.filterMap fun h =>
    if decide (n+h.length+1 ≤ k-t+1) && (base ||| unionSep d h == top)
    then some (g::(h++rest)) else none

def unaryAt (k t : Nat) (v : List Sig) (c : Cov) (a : Sig) : List Proposal :=
  (gateLists k t v (dropped [a] v) (v.length-1)
    (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]).map
    (fun w => ⟨t,w,.unary a⟩)

def unaryMoves (k t : Nat) (v : List Sig) : List Proposal :=
  let c := coverage (decide (0<t)) v
  v.flatMap (unaryAt k t v c)

def fastBinary (t : Nat) (v : List Sig) (a b : Sig) (ua ub : B) : List Proposal :=
  let rest := dropped [a,b] v
  let use : Bool → List Proposal := fun d =>
    let g := bin d a b
    if gateAvailable v g then [⟨t,g::rest,Move.binary d a b⟩] else []
  (if (ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 then use false else []) ++
    (if (ua &&& b.2) == 0 && (ub &&& a.2) == 0 then use true else [])

def slowBinary (k t : Nat) (v : List Sig) (c : Cov) (a b : Sig) : List Proposal :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  (gateLists k t v rest (v.length-2) mask (bin false a b) (allowedKeeps a b)).map
      (fun w => ⟨t,w,.binary false a b⟩) ++
    (gateLists k t v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)).map
      (fun w => ⟨t,w,.binary true a b⟩)

def pairs {α β : Type} (f : α → α → List β) : List α → List β
  | [] => []
  | a :: xs => xs.flatMap (f a) ++ pairs f xs

def binaryMoves (k t : Nat) (v : List Sig) : List Proposal :=
  let c := coverage (decide (0<t)) v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a,c.2.1 &&& sep false a))
    pairs (fun a b => fastBinary t v a.1 b.1 a.2 b.2) acts
  else pairs (slowBinary k t v c) v

def proposals : Nat → Nat → List Sig → List Proposal
  | 0,_,_ => []
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then [] else
    if v == [target] then [] else
    (if 0<t then unaryMoves k (t-1) v else []) ++ binaryMoves k t v

end PEqualNP.Outside.L_meta_670_aux.MemoChildren

namespace PEqualNP.Outside.L_meta_670_aux.MemoChildren

open LiveCheck

lemma root_binary_count : (proposals 15 0 raw).length = 72 := by decide +kernel

lemma root_one_not_count : (proposals 15 1 raw).length = 81 := by decide +kernel

lemma root_two_not_count : (proposals 15 2 raw).length = 90 := by decide +kernel

lemma root_metadata :
    (proposals 15 2 raw).all (fun p => p.wires.head? == some p.move.value) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_670_aux.MemoChildren
