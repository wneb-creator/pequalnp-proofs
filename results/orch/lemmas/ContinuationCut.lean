import PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760

noncomputable section cutCore
def topCut (F G : Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv F l m g k t z v y) (Nat.beq ph 1)) true
      (node (G (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startCut (F G : Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCut F G l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end cutCore
noncomputable def chkCut (F G : Nat → Nat → Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startCut F G l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma chkCut_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkCut (look (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K)
      (look1 (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K K) E Q Z K t H ph =
      chk E Q Z K t H ph := by
  simp only [chkCut, chk, frc_eq, st_eq, startCut, startv, topCut, topC]

lemma orFold_append {α : Type} (p : α → Bool) (xs ys : List α) :
    List.rec false (fun a _ ih => Bool.rec ih true (p a)) (xs ++ ys) =
      (List.rec false (fun a _ ih => Bool.rec ih true (p a)) xs ||
        List.rec false (fun a _ ih => Bool.rec ih true (p a)) ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append]
    rw [ih]
    cases p a <;> rfl

lemma nots_append (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v xs ys : List W) :
    nots f m g e n z q v (xs ++ ys) =
      (nots f m g e n z q v xs || nots f m g e n z q v ys) := by
  exact orFold_append _ xs ys

lemma nots_false_of_singletons (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v xs : List W) (h : ∀ w ∈ xs, nots f m g e n z q v [w] = false) :
    nots f m g e n z q v xs = false := by
  revert h
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    have hr := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    change nots f m g e n z q v ([a] ++ xs) = false
    rw [nots_append, ha, hr]
    rfl
abbrev WKey := Nat × Nat × Nat × Nat × Nat
abbrev CutState := Nat × Nat × Nat × List W
abbrev CutKey := Nat × Nat × Nat × List WKey

def wKey (w : W) : WKey := (w.s, w.a, w.b, w.c, w.r)
def wUnkey (w : WKey) : W := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩
def cutKey (s : CutState) : CutKey := (s.1, s.2.1, s.2.2.1, s.2.2.2.map wKey)
def cutUnkey (s : CutKey) : CutState := (s.1, s.2.1, s.2.2.1, s.2.2.2.map wUnkey)

lemma wUnkey_key (w : W) : wUnkey (wKey w) = w := by cases w; rfl
lemma cutUnkey_key (s : CutState) : cutUnkey (cutKey s) = s := by
  rcases s with ⟨k, t, z, v⟩
  simp only [cutUnkey, cutKey, List.map_map, Function.comp_def, wUnkey_key]
  change (k, t, z, List.map id v) = (k, t, z, v)
  rw [List.map_id]

lemma cutKey_injective : Function.Injective cutKey := by
  intro s t h
  have h' := congrArg cutUnkey h
  simpa only [cutUnkey_key] using h'

def patchCut (F : Nat → Nat → Nat → List W → Bool) (states : List CutState)
    (k t z : Nat) (v : List W) : Bool :=
  if cutKey (k, t, z, v) ∈ states.map cutKey then false else F k t z v

lemma patchCut_eq (F : Nat → Nat → Nat → List W → Bool) (states : List CutState)
    (h : ∀ s ∈ states, F s.1 s.2.1 s.2.2.1 s.2.2.2 = false) :
    patchCut F states = F := by
  funext k t z v
  unfold patchCut
  split_ifs with hm
  · obtain ⟨s, hs, he⟩ := List.mem_map.1 hm
    have he := cutKey_injective he
    subst s
    exact (h (k, t, z, v) hs).symm
  · rfl

end PEqualNP.Outside.L_meta_10760
