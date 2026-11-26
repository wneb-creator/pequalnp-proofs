import DirectDecode
import PreparedLinks

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

lemma map_read (f : Word → Word) (z : Word) (ws : List Word) (i : Nat) :
    (ws.map f).getD i (f z) = f (ws.getD i z) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? <;> rfl

def liveStep (code : Nat) (ws : List Word) : List Word :=
  (applyCode ⟨ws,[]⟩ code).live

lemma applyCode_live (st : State) (code : Nat) :
    (applyCode st code).live = liveStep code st.live := rfl

lemma liveStep_map (f : Word → Word) (fz : f Extended.zero = Extended.zero)
    (fb : ∀ d a b, f (Extended.bin d a b) = Extended.bin d (f a) (f b))
    (code : Nat) (ws : List Word) :
    (liveStep code ws).map f = liveStep code (ws.map f) := by
  have rd (i : Nat) : (ws.map f).getD i Extended.zero = f (ws.getD i Extended.zero) := by
    simpa only [fz] using map_read f Extended.zero ws i
  simp only [liveStep,applyCode,List.map_append,List.map_cons,List.map_take,List.map_drop,
    List.zipIdx_map,List.filter_map,List.map_map,Function.comp_def,Prod.map,rd,fb] <;> rfl

def decodeLiveFrom (getCode : Nat → Nat) (seed : List Word) : Nat → Nat → List Word
  | 0, _ => seed
  | fuel+1, i => if i=0 then seed else
      let code := getCode i
      liveStep code (decodeLiveFrom getCode seed fuel (code >>> 19))

lemma decodeStateBy_live (getCode : Nat → Nat) (fuel i : Nat) :
    (decodeStateBy getCode fuel i).live = decodeLiveFrom getCode Extended.initial fuel i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeStateBy,decodeLiveFrom]
    split
    · rfl
    · rw [applyCode_live,ih]

lemma decodeLiveFrom_map (f : Word → Word) (fz : f Extended.zero = Extended.zero)
    (fb : ∀ d a b, f (Extended.bin d a b) = Extended.bin d (f a) (f b))
    (getCode : Nat → Nat) (seed : List Word) (fuel i : Nat) :
    (decodeLiveFrom getCode seed fuel i).map f = decodeLiveFrom getCode (seed.map f) fuel i := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeLiveFrom]
    split
    · rfl
    · rw [liveStep_map f fz fb,ih]

lemma mapped_decodeStateBy (f : Word → Word) (fz : f Extended.zero = Extended.zero)
    (fb : ∀ d a b, f (Extended.bin d a b) = Extended.bin d (f a) (f b))
    (getCode : Nat → Nat) (fuel i : Nat) :
    (decodeStateBy getCode fuel i).live.map f =
      decodeLiveFrom getCode (Extended.initial.map f) fuel i := by
  rw [decodeStateBy_live]
  exact decodeLiveFrom_map f fz fb getCode Extended.initial fuel i

lemma moved_decodeStateBy (p : List Automorphism.Move) (getCode : Nat → Nat) (fuel i : Nat) :
    (decodeStateBy getCode fuel i).live.map (Automorphism.movedWord p) =
      decodeLiveFrom getCode (Extended.initial.map (Automorphism.movedWord p)) fuel i := by
  apply mapped_decodeStateBy
  · rw [Automorphism.moved_eq_rename]
    exact (Automorphism.rename_constants (Automorphism.movedRow p)).1
  · intro d a b
    simp only [Automorphism.moved_eq_rename,Automorphism.rename_bin]

end PEqualNP.Outside.L_meta_2373_aux.Cert18
