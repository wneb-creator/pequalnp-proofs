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
