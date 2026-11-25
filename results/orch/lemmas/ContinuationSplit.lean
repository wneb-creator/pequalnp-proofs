import Computational

namespace PEqualNP.Outside.L_meta_10760_aux

lemma rec_branch_or (p q : Bool) :
    Bool.rec (motive := fun _ => Bool) q true p =
      (Bool.rec (motive := fun _ => Bool) false true p || q) := by
  cases p <;> rfl

lemma rec_branch_or_simple (p q : Bool) :
    Bool.rec (motive := fun _ => Bool) q true p = (p || q) := by
  cases p <;> rfl

lemma rec_branch_distrib (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool) (a || b) true c =
      (Bool.rec (motive := fun _ => Bool) a true c ||
        Bool.rec (motive := fun _ => Bool) b true c) := by
  cases c <;> simp

lemma rec_guard_distrib (a b c : Bool) :
    Bool.rec (motive := fun _ => Bool) false (a || b) c =
      (Bool.rec (motive := fun _ => Bool) false a c ||
        Bool.rec (motive := fun _ => Bool) false b c) := by
  cases c <;> simp

noncomputable def notsOne (f : ℕ → ℕ → List W → Bool) (m g e n z q : ℕ)
    (v : List W) (a : W) : Bool := nots f m g e n z q v [a]

lemma nots_cons_split (f : ℕ → ℕ → List W → Bool) (m g e n z q : ℕ)
    (v : List W) (a : W) (r : List W) :
    nots f m g e n z q v (a :: r) =
      (notsOne f m g e n z q v a || nots f m g e n z q v r) := by
  exact rec_branch_or _ _

lemma nots_append_split (f : ℕ → ℕ → List W → Bool) (m g e n z q : ℕ)
    (v r s : List W) :
    nots f m g e n z q v (r ++ s) =
      (nots f m g e n z q v r || nots f m g e n z q v s) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    simp only [List.cons_append, nots_cons_split, ih, Bool.or_assoc]

lemma nots_filter_or (f : ℕ → ℕ → List W → Bool) (m g e n z q : ℕ)
    (v r : List W) (p₁ p₂ : W → Bool) :
    nots f m g e n z q v (r.filter fun w => p₁ w || p₂ w) =
      (nots f m g e n z q v (r.filter p₁) ||
        nots f m g e n z q v (r.filter p₂)) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases h₁ : p₁ a <;> cases h₂ : p₂ a <;>
      simp [h₁, h₂, nots_cons_split, ih,
        Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma prd_or_split (t : ℕ) (F G : ℕ → Bool) :
    prd t (fun x => F x || G x) = (prd t F || prd t G) := by
  cases t <;> rfl

lemma tst_or_split (d : Bool) (l e : ℕ) (v : List W) (F G : ℕ → Bool) :
    tst d l e v (fun x => F x || G x) = (tst d l e v F || tst d l e v G) := by
  cases h₀ : Nat.beq v.length e <;>
    cases h₁ : Nat.beq (Nat.succ v.length) e <;>
    cases h₂ : bip l (wst d l v) v [] <;>
    cases h₃ : flk l (wst d l v) v star <;>
    cases h₄ : rect d l (wst d l v) v [] <;>
      simp [tst, h₀, h₁, h₂, h₃, h₄]

lemma child_eval_or (F G : ℕ → List W → Bool) (g z : ℕ) (v : List W) :
    child (fun a r => F a r || G a r) g (fun h => h v) z =
      (child F g (fun h => h v) z || child G g (fun h => h v) z) := by
  simp only [child, st_eq]
  exact rec_guard_distrib _ _ _

lemma anySub_cons_split (d : Bool) (l : ℕ) (w : W) (v : List W)
    (c : ℕ) (h : List W → Bool) :
    anySub d l (w :: v) c h =
      (anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) ||
        bif Nat.beq (Nat.lor c (cov d l v)) l then anySub d l v c h else false) := by
  change Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h)
      (Nat.beq (Nat.lor c (cov d l v)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) = _
  rw [st_eq, rec_branch_or_simple, bR]

lemma anySub_or_split (d : Bool) (l : ℕ) (v : List W) (c : ℕ)
    (F G : List W → Bool) :
    anySub d l v c (fun r => F r || G r) =
      (anySub d l v c F || anySub d l v c G) := by
  induction v generalizing c F G with
  | nil => rfl
  | cons w v ih =>
    simp only [anySub_cons_split, ih]
    cases Nat.beq (Nat.lor c (cov d l v)) l <;>
      simp only [Bool.cond_false, Bool.cond_true, Bool.or_false]
    ac_rfl

noncomputable def mvSel (pick : W → Bool) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter pick))) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length

noncomputable def topSel (pick : W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvSel pick (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

noncomputable def startSel (pick : W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topSel pick l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

noncomputable def chkSel (pick : W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startSel pick l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

def notPick (i : ℕ) (w : W) : Bool :=
  if i < 7 then Nat.beq w.s (Nat.land (rawP.getD i 0) (mz 0))
  else !(rawP.any fun s => Nat.beq w.s (Nat.land s (mz 0)))

lemma mvSel_or_split (p q : W → Bool) (F : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mvSel (fun w => p w || q w) F l m g k t z v y =
      (mvSel p F l m g k t z v y || mvSel q F l m g k t z v y) := by
  simp only [mvSel]
  simp_rw [nots_filter_or]
  rw [prd_or_split]
  exact rec_branch_distrib _ _ _

lemma topSel_or_split (p q : W → Bool) (l m g K H ph k t z : ℕ) (v : List W) :
    topSel (fun w => p w || q w) l m g K H ph k t z v =
      (topSel p l m g K H ph k t z v || topSel q l m g K H ph k t z v) := by
  simp only [topSel]
  simp_rw [mvSel_or_split, rec_guard_distrib, rec_branch_distrib, tst_or_split]
  exact rec_branch_distrib _ _ _

lemma startSel_or_split (a b : W → Bool) (l m g B K t p H ph : ℕ) (v : List W) :
    startSel (fun w => a w || b w) l m g B K t p H ph v =
      (startSel a l m g B K t p H ph v || startSel b l m g B K t p H ph v) := by
  simp only [startSel]
  simp_rw [topSel_or_split, child_eval_or, rec_guard_distrib]

lemma chkSel_or_split (a b : W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkSel (fun w => a w || b w) E Q Z K t H ph =
      (chkSel a E Q Z K t H ph || chkSel b E Q Z K t H ph) := by
  simp only [chkSel, frc_eq, st_eq]
  simp_rw [startSel_or_split, anySub_or_split]

lemma mvSel_true (F : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mvSel (fun _ => true) F l m g k t z v y = mv F l m g k t z v y := by
  simp only [mvSel, List.filter_true, mv]

lemma chkSel_true (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkSel (fun _ => true) E Q Z K t H ph = chk E Q Z K t H ph := by
  simp only [chkSel, chk, startSel, startv, topSel, topC, mvSel_true]

lemma child_or_split (F G : ℕ → List W → Bool) (g z : ℕ)
    (mk : (List W → Bool) → Bool)
    (hmk : ∀ A B : List W → Bool, mk (fun r => A r || B r) = (mk A || mk B)) :
    child (fun a r => F a r || G a r) g mk z = (child F g mk z || child G g mk z) := by
  simp only [child, st_eq]
  rw [hmk]
  exact rec_guard_distrib _ _ _

lemma rm_or_split (x y : ℕ) (v : List W) (F G : List W → Bool) :
    rm x y v (fun r => F r || G r) = (rm x y v F || rm x y v G) := by
  simp only [rm_eq]

lemma scan_cons_split (p : X → Bool) (a : X) (r : List X) :
    scan p (a :: r) = (p a || scan p r) := by
  exact rec_branch_or_simple _ _

lemma scan_or_split (p q : X → Bool) (r : List X) :
    scan (fun a => p a || q a) r = (scan p r || scan q r) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    simp only [scan_cons_split, ih]
    ac_rfl

lemma chkSel_any_nonempty (ps : List (W → Bool)) (hne : ps ≠ [])
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkSel (fun w => ps.any fun p => p w) E Q Z K t H ph =
      ps.any (fun p => chkSel p E Q Z K t H ph) := by
  induction ps with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
    cases ps with
    | nil => simp only [List.any_cons, List.any_nil, Bool.or_false]
    | cons q qs =>
      rw [List.any_cons]
      change chkSel (fun w => p w || (q :: qs).any fun r => r w) E Q Z K t H ph = _
      rw [chkSel_or_split, ih (by simp)]

lemma chkSel_false_of_cover (ps : List (W → Bool)) (hne : ps ≠ [])
    (cover : ∀ w, ps.any (fun p => p w) = true)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ p ∈ ps, chkSel p E Q Z K t H ph = false) : chk E Q Z K t H ph = false := by
  have heq := chkSel_any_nonempty ps hne E Q Z K t H ph
  have hfun : (fun w => ps.any fun p => p w) = (fun _ => true) := funext cover
  rw [hfun, chkSel_true] at heq
  rw [heq]
  exact List.any_eq_false.mpr (fun p hp => by simp [h p hp])

def notPicks : List (W → Bool) := List.ofFn (fun i : Fin 8 => notPick i.val)

lemma rawP_ofFn : List.ofFn (fun i : Fin 7 => rawP.getD i.val 0) = rawP := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h₁ h₂
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    rfl

lemma notPicks_cover (w : W) : notPicks.any (fun p => p w) = true := by
  apply List.any_eq_true.mpr
  cases h : rawP.any (fun s => Nat.beq w.s (Nat.land s (mz 0))) with
  | false =>
    refine ⟨notPick 7, ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨(7 : Fin 8), rfl⟩
    · simp only [notPick, show ¬(7 < 7) from by omega, ↓reduceIte, h]
      rfl
  | true =>
    obtain ⟨s, hs, hb⟩ := List.any_eq_true.mp h
    rw [← rawP_ofFn] at hs
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hs
    refine ⟨notPick i.val, ?_, ?_⟩
    · exact List.mem_ofFn.mpr ⟨⟨i.val, by omega⟩, rfl⟩
    · simp only [notPick, i.isLt, ↓reduceIte]
      rw [hi]
      exact hb

lemma chk_of_notPicks (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ i : Fin 8, chkSel (notPick i.val) E Q Z K t H ph = false) :
    chk E Q Z K t H ph = false := by
  apply chkSel_false_of_cover notPicks (by simp [notPicks]) notPicks_cover
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact h i

end PEqualNP.Outside.L_meta_10760_aux
