import SliceProfiles

namespace PEqualNP.Outside.L_meta_2373.Live1024.CofactorMoves

private lemma bit_zero (i : Row) : bit i zero = false := by simp [bit, zero]
private lemma bit_one (i : Row) : bit i one = true := by
  unfold bit one
  rw [BitVec.getLsbD_allOnes]
  simp

abbrev Move := Sig × Sig × Row


def shifted (d r : Row) : Row :=
  if h : r.val < 1024-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(1024-d.val),by omega⟩


def backwards (d : Row) : Row := Fin.ofNat 1024 (1024-d.val)


def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r


def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)


def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)


theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 1024-d.val <;> simp [shifted,h,r.isLt]


theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp


theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _


theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl


def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r


def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a


theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)


theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm


def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w


theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)


def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))


theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩


theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL


theorem lower_lift {u : Bool} {roots : List NineSigned.Sig} {G : NineSigned.Sig} {L : Nat}
    (prior : NineSigned.Lower u roots G L) :
    Lower u (roots.map sliceNineLift) (sliceNineLift G) L := by
  intro p bank run hit
  have mapped := restrict_reach sliceNineSection run
  have same : ((roots.map sliceNineLift).map observe).map (restrictRows sliceNineSection) =
      roots.map NineSigned.observe := by
    simp only [List.map_map, Function.comp_def, restrict_sliceNineLift]
  rw [same] at mapped
  have available := restrict_available sliceNineSection hit
  rw [restrict_sliceNineLift] at available
  exact prior p _ (nine_reach_of_reach mapped) available

end PEqualNP.Outside.L_meta_2373.Live1024.CofactorMoves
