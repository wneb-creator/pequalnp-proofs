import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_670.LiveZeroBridge
namespace Weighted
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
def Live (target : Sig) : Nat → Nat → Finset Sig → Prop:=fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)),(proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target}:=fun M stop unary binary => @stop  h0
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a≠b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
end Weighted
namespace Normal
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
end Normal

theorem weighted_of_normal {T : Weighted.Sig} {k : Nat} {S : Finset Weighted.Sig}
    (h : Normal.Live false T k S) : Weighted.Live T k 0 S := by
  induction k generalizing S with
  | zero =>
      obtain ⟨rfl,hp⟩ := h
      exact Weighted.Live.stop hp
  | succ k ih =>
      obtain ⟨U,a,b,d,hd,rfl,ha,hb,ne,hf,hr⟩ := h
      have hd' : d=0 ∨ d=1 := by simp [Normal.allowed] at hd; omega
      rcases hd' with rfl | rfl
      · exact Weighted.Live.binary (d := false) ha hb ne hf (ih hr)
      · exact Weighted.Live.binary (d := true) ha hb ne hf (ih hr)

theorem normal_of_weighted {T : Weighted.Sig} {k : Nat} {S : Finset Weighted.Sig}
    (h : Weighted.Live T k 0 S) : Normal.Live false T k S := by
  apply h (fun k t S => t=0 → Normal.Live false T k S)
  · intro hp ht
    exact ⟨rfl,hp⟩
  · intro k t U a ha hf ih ht
    omega
  · intro k t U a b d ha hb ne hf ih ht
    refine ⟨U,a,b,if d then 1 else 0,?_,rfl,ha,hb,ne,?_,?_⟩
    · cases d <;> simp [Normal.allowed]
    · cases d <;> simpa [Normal.bin,Weighted.bin] using hf
    · cases d <;> simpa [Normal.bin,Weighted.bin] using ih ht
  · rfl

theorem live_zero_iff {T : Weighted.Sig} {k : Nat} {S : Finset Weighted.Sig} :
    Weighted.Live T k 0 S ↔ Normal.Live false T k S :=
  ⟨normal_of_weighted,weighted_of_normal⟩

end PEqualNP.Outside.L_meta_670.LiveZeroBridge
