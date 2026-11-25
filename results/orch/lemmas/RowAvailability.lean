import Mathlib

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 ||
    x 1 && x 2 ||
    x 2 && x 3 ||
    x 3 && x 4 ||
    x 4 && x 0 ||
    x 0 && x 5 ||
    x 1 && x 6 ||
    x 2 && x 7 ||
    x 3 && x 8 ||
    x 4 && x 9 ||
    x 5 && x 7 ||
    x 7 && x 9 ||
    x 9 && x 6 ||
    x 6 && x 8 ||
    x 8 && x 5


def relabel (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
    ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
    ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
    ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] v

lemma relabel_bijective : ∀ v : Fin 10, Function.Bijective (relabel v) := by
  intro v
  fin_cases v <;> decide

lemma relabel_last : ∀ v : Fin 10, relabel v 9 = v := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma relabel_edge : ∀ (v : Fin 10) (x : Fin 10 → Bool), edge (x ∘ relabel v) = edge x := by
  intro v x
  fin_cases v <;> dsimp [edge, relabel, Function.comp_def] <;> ac_rfl


namespace Live1024
abbrev Sig := BitVec 1024
def zero : Sig := 0
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
def observe (a : Sig) (r : Fin 1024) : Bool := bit r a
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
end Live1024

namespace NineSigned
abbrev Sig := BitVec 512
def zero : Sig := 0
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
def observe (a : Sig) (r : Fin 512) : Bool := bit r a
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]


def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8


end NineSigned

def rowMap (v : Fin 10) (r : Fin 512) : Fin 1024 :=
  Fin.ofNat 1024 (∑ i : Fin 9,
    if r.val.testBit i.val then 2 ^ (relabel v i.castSucc).val else 0)


namespace Live1024
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u = true ∧ inv v ∈ pool)
end Live1024
namespace NineSigned
lemma input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
end NineSigned

lemma rowMap_available_of
    (missing : ∀ (v : Fin 10) (r : Fin 512),
      Live1024.observe (Live1024.inputs.getD v.val Live1024.zero) (rowMap v r) = false)
    (remaining : ∀ (v : Fin 10) (j : Fin 9) (r : Fin 512),
      Live1024.observe (Live1024.inputs.getD (relabel v j.castSucc).val Live1024.zero)
        (rowMap v r) = NineSigned.observe (NineSigned.inputs.getD j.val NineSigned.zero) r)
    (v i : Fin 10) :
    Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (fun r => Live1024.observe (Live1024.inputs.getD i.val Live1024.zero) (rowMap v r)) := by
  by_cases hi : i = v
  · subst i
    exact Or.inr (Or.inl ⟨false, funext (missing v)⟩)
  · obtain ⟨j, hj⟩ := (relabel_bijective v).2 i
    have hne : j ≠ (9 : Fin 10) := by
      intro h
      subst j
      exact hi (hj.symm.trans (relabel_last v))
    have hjlt : j.val < 9 := by
      have hlt := j.isLt
      have hn : j.val ≠ 9 := fun h => hne (Fin.ext h)
      omega
    let k : Fin 9 := ⟨j.val, hjlt⟩
    have hk : relabel v k.castSucc = i := hj
    have heq :
        (fun r => Live1024.observe (Live1024.inputs.getD i.val Live1024.zero) (rowMap v r)) =
          NineSigned.observe (NineSigned.inputs.getD k.val NineSigned.zero) := by
      funext r
      rw [← hk]
      exact remaining v k r
    apply Or.inl
    rw [heq]
    apply List.mem_map.mpr
    refine ⟨NineSigned.inputs.getD k.val NineSigned.zero, ?_, rfl⟩
    have hm : NineSigned.inputs.getD k.val NineSigned.zero ∈
        List.ofFn (fun j : Fin 9 => NineSigned.inputs.getD j.val NineSigned.zero) :=
      List.mem_ofFn.mpr ⟨k, rfl⟩
    rw [NineSigned.input_list] at hm
    exact hm

end PEqualNP.Outside.L_meta_2373
