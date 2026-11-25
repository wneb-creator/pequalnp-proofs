import MvContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

noncomputable def lookFrontPick (pick : Nat → Nat → Nat → List W → Bool) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun fuel _ k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (fun k t z r => Bool.rec (motive := fun _ => Bool) false (look l m g K k t z r) (pick k t z r)) l m g k t z v y) true
        (node (fun z r => Bool.rec (motive := fun _ => Bool) false (look1 l m g K fuel (Nat.sub k 1) t z r) (pick (Nat.sub k 1) t z r)) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel

noncomputable def topDeepSel (pick : Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (lookFrontPick pick l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

noncomputable def startDeepSel (pick : Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topDeepSel pick l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

noncomputable def chkDeepSel (pick : Nat → Nat → Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startDeepSel pick l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma pick_guard_distrib (a p q : Bool) :
    Bool.rec (motive := fun _ => Bool) false a (p || q) =
      (Bool.rec (motive := fun _ => Bool) false a p ||
        Bool.rec (motive := fun _ => Bool) false a q) := by
  cases p <;> cases q <;> simp

lemma lookFrontPick_or_split (p q : ℕ → ℕ → ℕ → List W → Bool)
    (l m g K fuel k t z : ℕ) (v : List W) :
    lookFrontPick (fun k t z r => p k t z r || q k t z r) l m g K fuel k t z v =
      (lookFrontPick p l m g K fuel k t z v ||
        lookFrontPick q l m g K fuel k t z v) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [lookFrontPick, pick_guard_distrib, nodeS_or_split, mv_cont_or_split,
      rec_search_distrib, tst_or_split]
    exact rec_branch_distrib _ _ _

lemma lookFrontPick_or_fun (p q : ℕ → ℕ → ℕ → List W → Bool)
    (l m g K fuel : ℕ) :
    lookFrontPick (fun k t z r => p k t z r || q k t z r) l m g K fuel =
      (fun k t z r => lookFrontPick p l m g K fuel k t z r ||
        lookFrontPick q l m g K fuel k t z r) := by
  funext k t z r
  exact lookFrontPick_or_split p q l m g K fuel k t z r

lemma nodeCfs_or_split (H : ℕ) (F G : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) :
    node (fun z r => F z r || G z r) d l m g e n z v (fun h xs => pairsC H h (fs xs)) =
      (node F d l m g e n z v (fun h xs => pairsC H h (fs xs)) ||
        node G d l m g e n z v (fun h xs => pairsC H h (fs xs))) := by
  exact node_or_split F G d l m g e n z v (fun h xs => pairsC H h (fs xs))
    (fun A B xs => pairsC_or_split H A B (fs xs))

lemma rec_trigger_distrib (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool) c true (a || b) =
      (Bool.rec (motive := fun _ => Bool) c true a ||
        Bool.rec (motive := fun _ => Bool) c true b) := by
  cases c <;> simp only [rec_branch_or_simple, Bool.or_false, Bool.or_true]

lemma topDeepSel_or_split (p q : ℕ → ℕ → ℕ → List W → Bool)
    (l m g K H ph k t z : ℕ) (v : List W) :
    topDeepSel (fun k t z r => p k t z r || q k t z r) l m g K H ph k t z v =
      (topDeepSel p l m g K H ph k t z v ||
        topDeepSel q l m g K H ph k t z v) := by
  simp only [topDeepSel, lookFrontPick_or_fun, nodeCfs_or_split,
    rec_trigger_distrib, tst_or_split, rec_branch_distrib]

lemma startDeepSel_or_split (a b : ℕ → ℕ → ℕ → List W → Bool)
    (l m g B K t p H ph : ℕ) (v : List W) :
    startDeepSel (fun k t z r => a k t z r || b k t z r) l m g B K t p H ph v =
      (startDeepSel a l m g B K t p H ph v ||
        startDeepSel b l m g B K t p H ph v) := by
  simp only [startDeepSel]
  simp_rw [topDeepSel_or_split, child_eval_or, rec_guard_distrib]

lemma chkDeepSel_or_split (a b : ℕ → ℕ → ℕ → List W → Bool)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkDeepSel (fun k t z r => a k t z r || b k t z r) E Q Z K t H ph =
      (chkDeepSel a E Q Z K t H ph || chkDeepSel b E Q Z K t H ph) := by
  simp only [chkDeepSel, frc_eq, st_eq]
  simp_rw [startDeepSel_or_split, anySub_or_split]

lemma lookFrontPick_true (l m g K fuel k t z : ℕ) (v : List W) :
    lookFrontPick (fun _ _ _ _ => true) l m g K fuel k t z v =
      look1 l m g K fuel k t z v := by
  cases fuel <;> rfl

lemma lookFrontPick_true_fun (l m g K fuel : ℕ) :
    lookFrontPick (fun _ _ _ _ => true) l m g K fuel = look1 l m g K fuel := by
  funext k t z v
  exact lookFrontPick_true l m g K fuel k t z v

lemma chkDeepSel_true (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkDeepSel (fun _ _ _ _ => true) E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [chkDeepSel, chk, startDeepSel, startv, topDeepSel, topC,
    lookFrontPick_true_fun]

lemma chkDeepSel_any_nonempty (ps : List (ℕ → ℕ → ℕ → List W → Bool))
    (hne : ps ≠ []) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkDeepSel (fun k t z r => ps.any fun p => p k t z r) E Q Z K t H ph =
      ps.any (fun p => chkDeepSel p E Q Z K t H ph) := by
  induction ps with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
    cases ps with
    | nil => simp only [List.any_cons, List.any_nil, Bool.or_false]
    | cons q qs =>
      rw [List.any_cons]
      change chkDeepSel (fun k t z r => p k t z r || (q :: qs).any fun p => p k t z r)
        E Q Z K t H ph = _
      rw [chkDeepSel_or_split, ih (by simp)]

lemma chkDeepSel_false_of_cover (ps : List (ℕ → ℕ → ℕ → List W → Bool))
    (hne : ps ≠ []) (cover : ∀ k t z r, ps.any (fun p => p k t z r) = true)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ p ∈ ps, chkDeepSel p E Q Z K t H ph = false) :
    chk E Q Z K t H ph = false := by
  have heq := chkDeepSel_any_nonempty ps hne E Q Z K t H ph
  have hfun : (fun k t z r => ps.any fun p => p k t z r) = (fun _ _ _ _ => true) := by
    funext k t z r
    exact cover k t z r
  rw [hfun, chkDeepSel_true] at heq
  rw [heq]
  exact List.any_eq_false.mpr (fun p hp => by simp [h p hp])

lemma chkDeepSel_false_of_fin_cover {n : ℕ} (hn : 0 < n)
    (pick : Fin n → ℕ → ℕ → ℕ → List W → Bool)
    (cover : ∀ k t z r, ∃ i, pick i k t z r = true)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ i, chkDeepSel (pick i) E Q Z K t H ph = false) :
    chk E Q Z K t H ph = false := by
  apply chkDeepSel_false_of_cover (List.ofFn pick)
  · intro he
    have := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at this
    omega
  · intro k t z r
    obtain ⟨i, hi⟩ := cover k t z r
    exact List.any_eq_true.mpr ⟨pick i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  · intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact h i

end PEqualNP.Outside.L_meta_10760_aux
