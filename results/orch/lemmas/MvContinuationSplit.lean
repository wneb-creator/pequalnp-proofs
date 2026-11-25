import NodeContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

lemma child_rm_or_split (F G : ℕ → List W → Bool) (g z x y : ℕ) (v : List W) :
    child (fun a r => F a r || G a r) g (rm x y v) z =
      (child F g (rm x y v) z || child G g (rm x y v) z) := by
  exact child_or_split F G g z (rm x y v) (rm_or_split x y v)

noncomputable def notsBody (F : ℕ → ℕ → List W → Bool)
    (g e n z s : ℕ) (a : W) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false
      (child (F s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e)) true
    (Bool.rec (motive := fun _ => Bool) false
      (child (F s) g (rm a.s a.s v) z) (Nat.ble n e))

lemma notsBody_or_split (F G : ℕ → ℕ → List W → Bool)
    (g e n z s : ℕ) (a : W) (v : List W) :
    notsBody (fun s z r => F s z r || G s z r) g e n z s a v =
      (notsBody F g e n z s a v || notsBody G g e n z s a v) := by
  simp only [notsBody, child_eval_or, child_rm_or_split,
    rec_guard_distrib, rec_branch_or_simple]
  ac_rfl

lemma notsBody_or_fun (F G : ℕ → ℕ → List W → Bool)
    (g e n z s : ℕ) (a : W) :
    notsBody (fun s z r => F s z r || G s z r) g e n z s a =
      (fun r => notsBody F g e n z s a r || notsBody G g e n z s a r) := by
  funext r
  exact notsBody_or_split F G g e n z s a r

lemma notsBody_fun (F : ℕ → ℕ → List W → Bool)
    (g e n z s : ℕ) (a : W) :
    notsBody F g e n z s a = fun v =>
      (Bool.rec (motive := fun _ => Bool) false
        (child (F s) g (rm a.s a.s v) z) (Nat.ble n e) ||
      Bool.rec (motive := fun _ => Bool) false
        (child (F s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e)) := by
  funext v
  exact rec_branch_or_simple _ _

lemma notsOne_cont_or_split (F G : ℕ → ℕ → List W → Bool)
    (m g e n z q : ℕ) (v : List W) (a : W) :
    notsOne (fun s z r => F s z r || G s z r) m g e n z q v a =
      (notsOne F m g e n z q v a || notsOne G m g e n z q v a) := by
  change Bool.rec (motive := fun _ => Bool) false true
    (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor a.s m) fun s => st (Nat.sub z a.c) fun z =>
        ins ⟨s, a.b, a.a, a.c, 0⟩ v
          (notsBody (fun s z r => F s z r || G s z r) g e n z s a))
      false (Nat.beq (Nat.succ a.s) q)) = _
  simp only [st_eq]
  simp_rw [notsBody_or_fun, ins_or_split]
  cases h : Nat.beq (Nat.succ a.s) q <;>
    simp only [notsOne, nots, st_eq, h, rec_branch_or_simple, Bool.or_false,
      notsBody_fun]

lemma nots_cont_or_split (F G : ℕ → ℕ → List W → Bool)
    (m g e n z q : ℕ) (v r : List W) :
    nots (fun s z r => F s z r || G s z r) m g e n z q v r =
      (nots F m g e n z q v r || nots G m g e n z q v r) := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    simp only [nots_cons_split, notsOne_cont_or_split, ih]
    ac_rfl

lemma cv_or_split (d : Bool) (l : ℕ) (v : List W) (a b : Bool) :
    cv d l v (a || b) = (cv d l v a || cv d l v b) := by
  cases d
  · exact rec_guard_distrib _ _ _
  · rfl

lemma rec_search_distrib (a b c d : Bool) :
    Bool.rec (motive := fun _ => Bool) (a || b) true (c || d) =
      (Bool.rec (motive := fun _ => Bool) a true c ||
        Bool.rec (motive := fun _ => Bool) b true d) := by
  simp only [rec_branch_or_simple]
  ac_rfl

lemma nodeN_or_split (F G : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) :
    node (fun z r => F z r || G z r) d l m g e n z v pairsN =
      (node F d l m g e n z v pairsN || node G d l m g e n z v pairsN) := by
  exact node_or_split F G d l m g e n z v pairsN pairsN_or_split

lemma nodeP_or_split (q : ℕ) (F G : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) :
    node (fun z r => F z r || G z r) d l m g e n z v (pairsP q) =
      (node F d l m g e n z v (pairsP q) || node G d l m g e n z v (pairsP q)) := by
  exact node_or_split F G d l m g e n z v (pairsP q) (pairsP_or_split q)

lemma nodeQ_or_split (q q' : ℕ) (F G : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) :
    node (fun z r => F z r || G z r) d l m g e n z v (pairsQ q q') =
      (node F d l m g e n z v (pairsQ q q') || node G d l m g e n z v (pairsQ q q')) := by
  exact node_or_split F G d l m g e n z v (pairsQ q q') (pairsQ_or_split q q')

lemma nodeS_or_split (F G : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) :
    node (fun z r => F z r || G z r) d l m g e n z v pairsS =
      (node F d l m g e n z v pairsS || node G d l m g e n z v pairsS) := by
  exact node_or_split F G d l m g e n z v pairsS pairsS_or_split

lemma mv_cont_or_split (F G : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mv (fun k t z r => F k t z r || G k t z r) l m g k t z v y =
      (mv F l m g k t z v y || mv G l m g k t z v y) := by
  simp only [mv]
  simp only [nodeN_or_split, nodeP_or_split, nodeQ_or_split, tst_or_split,
    cv_or_split, nots_cont_or_split, prd_or_split, rec_search_distrib]

end PEqualNP.Outside.L_meta_10760_aux
