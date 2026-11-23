import MemoBoolFastTest
import StrictPrefixTest

namespace PEqualNP.Outside.L_meta_670_aux.MemoInvariant

open LiveCheck MemoBoolFast MemoLocalBoolFast

variable (Context : List Sig → Type)

lemma collect_sound_at (k : Nat)
    (evaluate : (t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo)
    (child : Child Context)
    (hev : ∀ m, Sound m →
      ResultSound k child.nots child.wires (evaluate child.nots child.wires (child.context ()) m))
    {a : Memo × List Entry} (ha : AccSound a) :
    AccSound (collect Context k evaluate a child) := by
  rcases a with ⟨m,es⟩
  rcases child with ⟨t,v,c⟩
  simp only [collect]
  split
  · exact ha
  · exact stash_sound (hev m ha.1) ha.2

lemma collect_fold_sound_on (k : Nat)
    (evaluate : (t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo)
    (children : List (Child Context))
    (hev : ∀ child ∈ children, ∀ m, Sound m →
      ResultSound k child.nots child.wires (evaluate child.nots child.wires (child.context ()) m))
    {a : Memo × List Entry} (ha : AccSound a) :
    AccSound (children.foldl (collect Context k evaluate) a) := by
  induction children generalizing a with
  | nil => exact ha
  | cons child children ih =>
      have ht : ∀ c ∈ children, ∀ m, Sound m →
          ResultSound k c.nots c.wires (evaluate c.nots c.wires (c.context ()) m) := by
        intro c hc
        exact hev c (List.mem_cons_of_mem _ hc)
      exact ih ht (collect_sound_at Context k evaluate child
        (hev child List.mem_cons_self) ha)

variable (Inv : (v : List Sig) → Context v → Prop)
variable (cut : (k t : Nat) → (v : List Sig) → Context v → Bool)
variable (next : (k t : Nat) → (v : List Sig) → Context v → List (Child Context))
variable (retain : Nat → Nat → List Sig → Bool)

lemma guarded_sound_at
    {k t : Nat} {v : List Sig} {c : Context v} {m : Memo}
    (hcut : v.Nodup → cut k t v c = true → Impossible k t v)
    {evaluate : Memo → Bool × Memo} (hm : Sound m)
    (he : v.Nodup → ResultSound k t v (evaluate m)) :
    ResultSound k t v (MemoLocalBoolFast.guarded Context cut k t v c m evaluate) := by
  unfold MemoLocalBoolFast.guarded
  split
  · rename_i hh
    exact ⟨hm,fun _ => MemoBoolFast.hit_sound hm hh⟩
  · split
    · rename_i hv
      have hn : v.Nodup := BoolNodup.sound hv
      split
      · rename_i hc
        exact ⟨hm,fun _ => hcut hn hc⟩
      · exact he hn
    · exact ⟨hm,by simp⟩

lemma solve_sound
    (cutSound : ∀ k t v c, Inv v c → v.Nodup → cut k t v c = true → Impossible k t v)
    (nextValid : ∀ k t v c, Inv v c →
      ∀ child ∈ next k t v c, Inv child.wires (child.context ()))
    (k t : Nat) (v : List Sig) (c : Context v) (m : Memo)
    (hc : Inv v c) (hm : Sound m) :
    ResultSound k t v (MemoLocalBoolFast.solve Context cut next retain k t v c m) := by
  induction k generalizing t v c m with
  | zero =>
      rw [MemoLocalBoolFast.solve]
      apply guarded_sound_at Context cut (cutSound 0 t v c hc) hm
      intro hv
      exact finish_sound retain hm (exclude_search hv)
  | succ k ih =>
      rw [MemoLocalBoolFast.solve]
      apply guarded_sound_at Context cut (cutSound (k+1) t v c hc) hm
      intro hv
      apply MemoLocalBoolFast.complete_sound retain hv
      apply collect_fold_sound_on Context k (MemoLocalBoolFast.solve Context cut next retain k)
      · intro child hchild memo hmem
        exact ih child.nots child.wires (child.context ()) memo
          (nextValid (k+1) t v c hc child hchild) hmem
      · exact ⟨hm,by simp [EntriesSound]⟩

end PEqualNP.Outside.L_meta_670_aux.MemoInvariant

namespace PEqualNP.Outside.L_meta_670_aux.DynamicRaw

open LiveCheck DynamicLeaf

abbrev RawContext (n : Nat) (_ : List Sig) := Context n

def cut {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (_v : List Sig)
    (ctx : Context n) : Bool :=
  ((List.finRange n).any fun i =>
    !(Base1007.unionSep (decide (0<t)) (ctx i).vals == Base1007.top)) ||
      pruned oracles k ctx

lemma cut_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hctx : Valid oracles v ctx)
    (hv : v.Nodup) (hc : cut oracles k t v ctx = true) : Impossible k t v := by
  rcases Bool.or_eq_true_iff.mp hc with hcover | hprefix
  · obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hcover
    have hf : Base1007.unionSep (decide (0<t)) (ctx i).vals ≠ Base1007.top := by
      intro he
      simp only [he,beq_self_eq_true,Bool.not_true,Bool.false_eq_true] at hbad
    exact ProjectedCoverage.directed_failure (htarget i) (oracles i).mapNeg
      (oracles i).mapBin (hctx i) hf
  · exact pruned_sound hsound hv hctx hprefix

def next {n : Nat} (oracles : Fin n → Oracle) (k t : Nat) (v : List Sig)
    (ctx : Context n) : List (MemoBoolFast.Child (RawContext n)) :=
  List.map (fun (p : MemoChildren.Proposal) =>
    { nots := p.nots
      wires := p.wires
      context := fun (_ : Unit) =>
        StrictPrefix.updateWithRecipe oracles v p.wires ctx (some (DynamicCovered.recipe p.move)) })
    (MemoChildren.proposals k t v)

lemma next_valid {n : Nat} (oracles : Fin n → Oracle)
    (k t : Nat) (v : List Sig) (ctx : Context n) (hctx : Valid oracles v ctx) :
    ∀ child ∈ next oracles k t v ctx, Valid oracles child.wires (child.context ()) := by
  intro child hchild
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hchild
  exact StrictPrefix.updateWithRecipe_valid hctx p.wires (some (DynamicCovered.recipe p.move))

def runFast {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) :
    Bool × MemoBoolFast.Memo :=
  MemoLocalBoolFast.solve (RawContext n) (cut oracles) (next oracles)
    (fun _ _ _ => true) k t v (FastRecipe.initial oracles rho hint v programs) .empty

def fastLeafCheck {n : Nat} (oracles : Fin n → Oracle)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (k t : Nat) (v : List Sig)
    (programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat) : Bool :=
  !(runFast oracles rho hint k t v programs).1

lemma fastLeafCheck_sound {n : Nat} (oracles : Fin n → Oracle)
    (hsound : ∀ i, (oracles i).Sound)
    (htarget : ∀ i, (oracles i).project target = Base1007.target)
    (rho : Fin n → Fin 9 → Base1007.Sig) (hint : Sig → Nat)
    (hr : ∀ i, rho i = (oracles i).project ∘ FastRecipe.source)
    {k t : Nat} {v : List Sig}
    {programs : Fin n → List PEqualNP.CircuitLowerBounds.Gate × List Nat}
    (hc : fastLeafCheck oracles rho hint k t v programs = true) : Impossible k t v := by
  have hs := MemoInvariant.solve_sound (RawContext n) (Valid oracles) (cut oracles)
    (next oracles) (fun _ _ _ => true) (cut_sound oracles hsound htarget) (next_valid oracles)
    k t v (FastRecipe.initial oracles rho hint v programs) .empty
    (FastRecipe.initial_valid oracles rho hint hr v programs)
    (show MemoBoolFast.Sound .empty from trivial)
  apply hs.2
  change (runFast oracles rho hint k t v programs).1 = false
  unfold fastLeafCheck at hc
  cases h : (runFast oracles rho hint k t v programs).1 with
  | false => rfl
  | true => simp only [h,Bool.not_true,Bool.false_eq_true] at hc

end PEqualNP.Outside.L_meta_670_aux.DynamicRaw

#print axioms PEqualNP.Outside.L_meta_670_aux.MemoInvariant.solve_sound
#print axioms PEqualNP.Outside.L_meta_670_aux.DynamicRaw.fastLeafCheck_sound
