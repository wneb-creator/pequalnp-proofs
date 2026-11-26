import DecodeHom

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

lemma map_readWith {α β : Type} (f : α → β) (z : α) (ws : List α) (i : Nat) :
    (ws.map f).getD i (f z) = f (ws.getD i z) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

def liveStepWith {α : Type} (zero : α) (bin : Nat → α → α → α)
    (code : Nat) (ws : List α) : List α :=
  let ai := code &&& 31
  let bi := (code >>> 5) &&& 31
  let op := (code >>> 10) &&& 3
  let ka := code.testBit 12
  let kb := code.testBit 13
  let pos := (code >>> 14) &&& 31
  let a := ws.getD ai zero
  let b := ws.getD bi zero
  let rest := (ws.zipIdx.filter fun (_,i) =>
    (i != ai || ka) && (i != bi || kb)).map Prod.fst
  let z := bin op a b
  rest.take pos ++ z :: rest.drop pos

lemma liveStepWith_word (code : Nat) (ws : List Word) :
    liveStepWith Extended.zero Extended.bin code ws = liveStep code ws := rfl

lemma liveStepWith_map {α β : Type} (zeroA : α) (binA : Nat → α → α → α)
    (zeroB : β) (binB : Nat → β → β → β) (f : α → β)
    (fz : f zeroA = zeroB)
    (fb : ∀ d a b, f (binA d a b) = binB d (f a) (f b))
    (code : Nat) (ws : List α) :
    (liveStepWith zeroA binA code ws).map f =
      liveStepWith zeroB binB code (ws.map f) := by
  have rd (i : Nat) : (ws.map f).getD i zeroB = f (ws.getD i zeroA) := by
    simpa only [fz] using map_readWith f zeroA ws i
  simp only [liveStepWith,List.map_append,List.map_cons,List.map_take,List.map_drop,
    List.zipIdx_map,List.filter_map,List.map_map,Function.comp_def,Prod.map,rd,fb]; rfl

def decodeLiveFromWith {α : Type} (zero : α) (bin : Nat → α → α → α)
    (getCode : Nat → Nat) (seed : List α) : Nat → Nat → List α
  | 0, _ => seed
  | fuel+1, i => if i=0 then seed else
      let code := getCode i
      liveStepWith zero bin code (decodeLiveFromWith zero bin getCode seed fuel (code >>> 19))

lemma decodeLiveFromWith_map {α β : Type} (zeroA : α) (binA : Nat → α → α → α)
    (zeroB : β) (binB : Nat → β → β → β) (f : α → β)
    (fz : f zeroA = zeroB)
    (fb : ∀ d a b, f (binA d a b) = binB d (f a) (f b))
    (getCode : Nat → Nat) (seed : List α) (fuel i : Nat) :
    (decodeLiveFromWith zeroA binA getCode seed fuel i).map f =
      decodeLiveFromWith zeroB binB getCode (seed.map f) fuel i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeLiveFromWith]
    split
    · rfl
    · rw [liveStepWith_map zeroA binA zeroB binB f fz fb,ih]

lemma decodeStateBy_liveWith (getCode : Nat → Nat) (fuel i : Nat) :
    (decodeStateBy getCode fuel i).live =
      decodeLiveFromWith Extended.zero Extended.bin getCode Extended.initial fuel i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeStateBy,decodeLiveFromWith]
    split
    · rfl
    · rw [applyCode_live,←liveStepWith_word,ih]

lemma mapped_decodeStateByWith {α : Type} (zero : α) (bin : Nat → α → α → α)
    (f : Word → α) (fz : f Extended.zero = zero)
    (fb : ∀ d a b, f (Extended.bin d a b) = bin d (f a) (f b))
    (getCode : Nat → Nat) (fuel i : Nat) :
    (decodeStateBy getCode fuel i).live.map f =
      decodeLiveFromWith zero bin getCode (Extended.initial.map f) fuel i := by
  rw [decodeStateBy_liveWith]
  exact decodeLiveFromWith_map Extended.zero Extended.bin zero bin f fz fb
    getCode Extended.initial fuel i

end PEqualNP.Outside.L_meta_2373_aux.Cert18
