namespace PEqualNP.Outside.L_meta_670_aux.MemoLocalBoolFast

open LiveCheck MemoBoolFast

def EntriesSound (es : List Entry) : Prop :=
  ∀ e ∈ es, Impossible e.budget e.nots e.wires

def localHit (k t : Nat) (v : List Sig) (es : List Entry) : Bool :=
  es.any fun e =>
    decide (k ≤ e.budget) && e.nots == t && v.isPerm e.wires

lemma localHit_sound {k t : Nat} {v : List Sig} {es : List Entry}
    (hs : EntriesSound es) (hh : localHit k t v es = true) : Impossible k t v := by
  obtain ⟨e,he,hgood⟩ := List.any_eq_true.mp hh
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.isPerm_iff] at hgood
  obtain ⟨⟨hk,ht⟩,hp⟩ := hgood
  intro n hn hl
  apply hs e he n (by omega)
  have heq : v.toFinset = e.wires.toFinset := by
    ext a
    simpa only [List.mem_toFinset] using hp.mem_iff
  rw [ht,← heq]
  exact hl

def answer (k t : Nat) (v : List Sig) (m : Memo) (es : List Entry) : Bool :=
  !(hit k t v m || localHit k t v es)

lemma answer_false {k t : Nat} {v : List Sig} {m : Memo} {es : List Entry}
    (hm : Sound m) (he : EntriesSound es)
    (ha : answer k t v m es = false) : Impossible k t v := by
  have hh : hit k t v m || localHit k t v es = true := by
    unfold answer at ha
    cases h : hit k t v m || localHit k t v es <;> simp_all
  simp only [Bool.or_eq_true] at hh
  rcases hh with hh | hh
  · exact hit_sound hm hh
  · exact localHit_sound he hh

def AccSound (a : Memo × List Entry) : Prop :=
  Sound a.1 ∧ EntriesSound a.2

def withEntry {α : Type} (k t : Nat) (v : List Sig)
    (es : List Entry) (f : List Entry → α) : α :=
  forceNat k fun k' => forceNat t fun t' => forceWires v fun xs =>
    f (⟨k',t',xs⟩ :: es)

lemma withEntry_eq {α : Type} (k t : Nat) (v : List Sig)
    (es : List Entry) (f : List Entry → α) :
    withEntry k t v es f = f (⟨k,t,v⟩ :: es) := by
  simp only [withEntry,forceNat_eq,forceWires_eq]

def stash (k t : Nat) (v : List Sig) : Bool × Memo → List Entry → Memo × List Entry
  | (true,m), es => (m,es)
  | (false,m), es =>
      if hit k t v m then (m,es)
      else withEntry k t v es fun xs => (m,xs)

lemma stash_sound {k t : Nat} {v : List Sig} {r : Bool × Memo} {es : List Entry}
    (hr : ResultSound k t v r) (he : EntriesSound es) :
    AccSound (stash k t v r es) := by
  rcases r with ⟨b,m⟩
  cases b with
  | true => exact ⟨hr.1,he⟩
  | false =>
      simp only [stash]
      split
      · exact ⟨hr.1,he⟩
      · rw [withEntry_eq]
        refine ⟨hr.1,?_⟩
        intro e hem
        rcases List.mem_cons.mp hem with rfl | hem
        · exact hr.2 rfl
        · exact he e hem

variable (Context : List Sig → Type)

def collect (k : Nat)
    (evaluate : (t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo) :
    Memo × List Entry → Child Context → Memo × List Entry
  | (m,es), ⟨t,v,c⟩ =>
      if hit k t v m || localHit k t v es then (m,es)
      else stash k t v (evaluate t v (c ()) m) es

lemma collect_sound (k : Nat)
    (evaluate : (t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo)
    (hev : ∀ t v c m, Sound m → ResultSound k t v (evaluate t v c m))
    {a : Memo × List Entry} (ha : AccSound a) (child : Child Context) :
    AccSound (collect Context k evaluate a child) := by
  rcases a with ⟨m,es⟩
  rcases child with ⟨t,v,c⟩
  simp only [collect]
  split
  · exact ha
  · exact stash_sound (hev t v (c ()) m ha.1) ha.2

lemma collect_fold_sound (k : Nat)
    (evaluate : (t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo)
    (hev : ∀ t v c m, Sound m → ResultSound k t v (evaluate t v c m))
    (children : List (Child Context)) {a : Memo × List Entry} (ha : AccSound a) :
    AccSound (children.foldl (collect Context k evaluate) a) := by
  induction children generalizing a with
  | nil => exact ha
  | cons child children ih =>
      exact ih (collect_sound Context k evaluate hev ha child)

variable (cut : (k t : Nat) → (v : List Sig) → Context v → Bool)
variable (next : (k t : Nat) → (v : List Sig) → Context v → List (Child Context))
variable (retain : Nat → Nat → List Sig → Bool)

def guarded (k t : Nat) (v : List Sig) (c : Context v)
    (m : Memo) (evaluate : Memo → Bool × Memo) : Bool × Memo :=
  if hit k t v m then (false,m)
  else if BoolNodup.check v then
    if cut k t v c then (false,m) else evaluate m
  else (true,m)

lemma guarded_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    {k t : Nat} {v : List Sig} {c : Context v} {m : Memo}
    {evaluate : Memo → Bool × Memo} (hm : Sound m)
    (he : v.Nodup → ResultSound k t v (evaluate m)) :
    ResultSound k t v (guarded Context cut k t v c m evaluate) := by
  unfold guarded
  split
  · rename_i hh
    exact ⟨hm,fun _ => hit_sound hm hh⟩
  · split
    · rename_i hv
      have hn : v.Nodup := BoolNodup.sound hv
      split
      · rename_i hc
        exact ⟨hm,fun _ => cutSound k t v c hn hc⟩
      · exact he hn
    · exact ⟨hm,by simp⟩

def complete (k t : Nat) (v : List Sig) : Memo × List Entry → Bool × Memo
  | (m,es) =>
      finish retain (k+1) t v
        (stepTest k t v (fun w => answer k (t-1) w m es)
          (fun w => answer k t w m es)) m

lemma complete_sound {k t : Nat} {v : List Sig} {a : Memo × List Entry}
    (hv : v.Nodup) (ha : AccSound a) :
    ResultSound (k+1) t v (complete retain k t v a) := by
  rcases a with ⟨m,es⟩
  apply finish_sound retain ha.1
  apply exclude_step hv
  · intro w hw
    exact answer_false ha.1 ha.2 hw
  · intro w hw
    exact answer_false ha.1 ha.2 hw

def solve : (k t : Nat) → (v : List Sig) → Context v → Memo → Bool × Memo
  | 0,t,v,c,m => guarded Context cut 0 t v c m fun m' =>
      finish retain 0 t v (search 0 t v) m'
  | k+1,t,v,c,m => guarded Context cut (k+1) t v c m fun m' =>
      complete retain k t v
        ((next (k+1) t v c).foldl
          (collect Context k (solve k)) (m',[]))

lemma solve_sound
    (cutSound : ∀ k t v c, v.Nodup → cut k t v c = true → Impossible k t v)
    (k t : Nat) (v : List Sig) (c : Context v) (m : Memo) (hm : Sound m) :
    ResultSound k t v (solve Context cut next retain k t v c m) := by
  induction k generalizing t v c m with
  | zero =>
      rw [solve]
      apply guarded_sound Context cut cutSound hm
      intro hv
      exact finish_sound retain hm (exclude_search hv)
  | succ k ih =>
      rw [solve]
      apply guarded_sound Context cut cutSound hm
      intro hv
      apply complete_sound retain hv
      apply collect_fold_sound Context k (solve Context cut next retain k)
      · intro u w d memo hmem
        exact ih u w d memo hmem
      · exact ⟨hm,by simp [EntriesSound]⟩

end PEqualNP.Outside.L_meta_670_aux.MemoLocalBoolFast
