namespace PEqualNP.Outside.L_meta_2592_aux.SingleReadTrace

def read (w : List Bool) (i : Nat) : Bool := (w[i]?).getD false

def execute : List ((List Bool → Bool) × List Nat) → List Bool → List Bool
  | [], w => w
  | g :: gs, w => execute gs (w ++ [g.1 (g.2.map (read w))])

def shifted : List ((List Bool → Bool) × List Nat) → List Bool → List Bool
  | [], w => w
  | g :: gs, w => shifted gs (w ++ [g.1 (g.2.map (fun i => read w (i - 1)))])

theorem execute_append (pre post : List ((List Bool → Bool) × List Nat)) (w : List Bool) :
    execute (pre ++ post) w = execute post (execute pre w) := by
  induction pre generalizing w with
  | nil => rfl
  | cons g pre ih =>
    simp only [List.cons_append, execute]
    exact ih _

theorem execute_foldl (gs : List ((List Bool → Bool) × List Nat)) (w : List Bool) :
    execute gs w = gs.foldl (fun w g => w ++ [g.1 (g.2.map (read w))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons, execute]
    exact ih _

theorem read_cons_nonzero (b : Bool) (w : List Bool) (i : Nat) (hi : i ≠ 0) :
    read (b :: w) i = read w (i - 1) := by
  simp [read, List.getElem?_cons, hi]

theorem execute_ignores_head (gs : List ((List Bool → Bool) × List Nat))
    (unread : ∀ g ∈ gs, 0 ∉ g.2) (b : Bool) (w : List Bool) :
    execute gs (b :: w) = b :: shifted gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have head := unread g (by simp)
    have tail : ∀ h ∈ gs, 0 ∉ h.2 := fun h mem => unread h (by simp [mem])
    have args : g.2.map (read (b :: w)) = g.2.map (fun i => read w (i - 1)) := by
      apply List.map_congr_left
      intro i mem
      exact read_cons_nonzero b w i (fun eq => head (eq ▸ mem))
    simp only [execute, shifted, args, List.cons_append]
    exact ih tail _

theorem or_single_read_factor
    (pre post : List ((List Bool → Bool) × List Nat))
    (preUnread : ∀ g ∈ pre, 0 ∉ g.2)
    (postUnread : ∀ g ∈ post, 0 ∉ g.2)
    (i out : Nat) (hi : i ≠ 0) (ho : out ≠ 0)
    (b : Bool) (w : List Bool) :
    read (execute (pre ++ ((fun xs => xs.any id), [0, i]) :: post) (b :: w)) out =
      read (shifted post (shifted pre w ++ [b || read (shifted pre w) (i - 1)]))
        (out - 1) := by
  rw [execute_append, execute_ignores_head pre preUnread]
  simp only [execute]
  have gate : (([0, i] : List Nat).map (read (b :: shifted pre w))).any id =
      b || read (shifted pre w) (i - 1) := by
    simp [read, List.getElem?_cons, hi]
  rw [gate, List.cons_append, execute_ignores_head post postUnread]
  exact read_cons_nonzero b _ out ho

theorem and_single_read_factor
    (pre post : List ((List Bool → Bool) × List Nat))
    (preUnread : ∀ g ∈ pre, 0 ∉ g.2)
    (postUnread : ∀ g ∈ post, 0 ∉ g.2)
    (i out : Nat) (hi : i ≠ 0) (ho : out ≠ 0)
    (b : Bool) (w : List Bool) :
    read (execute (pre ++ ((fun xs => xs.all id), [0, i]) :: post) (b :: w)) out =
      read (shifted post (shifted pre w ++ [b && read (shifted pre w) (i - 1)]))
        (out - 1) := by
  rw [execute_append, execute_ignores_head pre preUnread]
  simp only [execute]
  have gate : (([0, i] : List Nat).map (read (b :: shifted pre w))).all id =
      b && read (shifted pre w) (i - 1) := by
    simp [read, List.getElem?_cons, hi]
  rw [gate, List.cons_append, execute_ignores_head post postUnread]
  exact read_cons_nonzero b _ out ho

end PEqualNP.Outside.L_meta_2592_aux.SingleReadTrace
