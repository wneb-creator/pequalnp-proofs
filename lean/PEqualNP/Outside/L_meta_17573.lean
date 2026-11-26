import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17573

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht, List.length_append, hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

theorem getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

def up (k i : ℕ) : ℕ := if i < k then i else i + 1

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
  unfold up eraseRedirect
  split_ifs <;> omega

theorem sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
    (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
    V.length = U.length + 1 →
    ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
      ∀ g ∈ rest, n + m ∉ g.inputs) →
    ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
      (rest.foldl step V).getD (up (n + m) i) false
  | [], U, V, hrel, _, _, _ => by simpa using hrel
  | g :: rest, U, V, hrel, hk, hlen, hS => by
    have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hS with ⟨hS, -⟩ | hS
        · simpa [eraseRedirect] using hS
        · exact absurd hr (hS g (List.mem_cons_self ..))
      · rw [hrel, up_redir n m p r hrk]
    set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
    have hU : step U (ren n m p g) = U ++ [a] := by
      simp only [step, ren, List.map_map]
      congr 3
      exact List.map_congr_left fun r hr => hread r hr
    have hV : step V g = V ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, hU, hV]
    apply sim n m p rest
    · intro i
      rcases lt_trichotomy i U.length with hi | rfl | hi
      · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
      · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
        rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
        simp
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
    · simp; omega
    · simp; omega
    · rcases hS with ⟨hS, hp⟩ | hS
      · left
        refine ⟨?_, ?_⟩
        · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
          rcases hp with hp | hp
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
          · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
            rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
            exact hS
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; simp at hp ⊢; omega
      · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

theorem erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
    (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
    (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval y = C.eval y := by
  obtain ⟨hg, ho⟩ := erase_gates n C m p hm
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set A := (C.gates.take m).foldl step y with hA
  have hAl : A.length = n + m := by
    rw [hA, fold_length, hy, List.length_take]; omega
  set rest := C.gates.drop (m + 1) with hrest
  have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
  have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
    rw [wires_eq, hg, List.foldl_append]
  have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
  have hWl : (C.wires y).length = n + C.gates.length := by
    rw [wires_eq, fold_length, hy]
  have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
    intro i hi
    rw [hW, fold_getD_lt _ _ _ (by omega)]
  have hsim := sim n m p rest A (step A C.gates[m]) (by
      intro i
      by_cases hi : i < n + m
      · simp only [up, if_pos hi, step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [up, if_neg hi]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
    (by omega) hVl (by
      rcases hc with hc | ⟨-, hc⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hstable _ (by omega)]
          rcases hp with hp | hp
          · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
          · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; omega
      · exact Or.inr hc)
  unfold Circuit.eval
  rw [ho, hW', hsim, ← hW]
  by_cases hout : C.output = n + m
  · rcases hc with hc | ⟨hc, -⟩
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout]
      rcases hp with hp | hp
      · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
        rw [hu]; exact hc.symm
      · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
        rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · exact absurd hout hc
  · rw [up_redir n m p _ hout]

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  unfold Circuit.size
  rw [(erase_gates n C m p hm).1]
  simp
  omega

theorem erase_fanin (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hC : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (eraseGate n C m p) := by
  intro g hg
  rw [(erase_gates n C m p hm).1, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g' (List.mem_of_mem_drop hg')
    exact ⟨h1, by simpa [ren] using h2⟩

theorem erase_prefix (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i < n + m) :
    ((eraseGate n C m p).wires x).getD i false = (C.wires x).getD i false := by
  have hc : i < ((C.gates.take m).foldl step x).length := by
    rw [fold_length, hx, List.length_take, Nat.min_eq_left (by omega)]
    exact hi
  rw [wires_eq, (erase_gates n C m p hm).1, List.foldl_append, fold_getD_lt _ _ _ hc, wires_eq]
  conv_rhs => rw [← List.take_append_drop m C.gates, List.foldl_append]
  exact (fold_getD_lt _ _ _ hc).symm

theorem deleteMany (n : ℕ) (S : Set (List Bool)) (hS : ∀ x ∈ S, x.length = n)
    (s : Finset ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (hb : ∀ i ∈ s, i < C.size)
    (he : ∀ i ∈ s, ∃ p < n+i, ∀ x ∈ S,
      (C.wires x).getD (n+i) false = (C.wires x).getD p false) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      D.size + s.card ≤ C.size ∧ ∀ x ∈ S, D.eval x = C.eval x := by
  induction s using Finset.induction_on_max generalizing C with
  | empty => exact ⟨C, hC, by simp, fun _ _ => rfl⟩
  | insert m s hlt ih =>
    have hm : m < C.gates.length := hb m (Finset.mem_insert_self _ _)
    obtain ⟨p,hp,hpEq⟩ := he m (Finset.mem_insert_self _ _)
    let T := eraseGate n C m p
    have hT : PEqualNP.MetaComplexity.FanInTwo T := erase_fanin n C m p hm hC
    have hTs : T.size + 1 = C.size := erase_size n C m p hm
    have hTb : ∀ i ∈ s, i < T.size := by
      intro i hi
      have h := hlt i hi
      unfold Circuit.size at *
      omega
    have hTe : ∀ i ∈ s, ∃ q < n+i, ∀ x ∈ S,
        (T.wires x).getD (n+i) false = (T.wires x).getD q false := by
      intro i hi
      obtain ⟨q,hq,hqEq⟩ := he i (Finset.mem_insert_of_mem hi)
      refine ⟨q,hq,fun x hx => ?_⟩
      have h := hlt i hi
      rw [erase_prefix n C m p hm x (hS x hx) _ (by omega),
        erase_prefix n C m p hm x (hS x hx) _ (by omega)]
      exact hqEq x hx
    obtain ⟨D,hD,hDsize,hDeval⟩ := ih T hT hTb hTe
    have hnot : m ∉ s := fun h => (Nat.lt_irrefl m) (hlt m h)
    refine ⟨D,hD,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hnot]
      omega
    · intro x hx
      exact (hDeval x hx).trans (erase_eval n C m p x (hS x hx) hm (.inl hp) (.inl (hpEq x hx)))

end PEqualNP.Outside.L_meta_17573

open PEqualNP.Outside.L_meta_17573

theorem PEqualNP.Outside.L_meta_17573 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Set (List Bool)) (x4 : Finset (Fin x1.size)), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x6 ∈ x3, x6.length = x2) → (∀ x7 ∈ x4, ∃ x9 < x2 + ↑x7, ∀ x10 ∈ x3, (x1.wires x10).getD (x2 + ↑x7) Bool.false = (x1.wires x10).getD x9 Bool.false) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + x4.card ≤ x1.size ∧ ∀ x9 ∈ x3, x8.eval x9 = x1.eval x9) := by
  intro C n S s hC hS hs
  let u := s.image (fun i => i.val)
  have hcard : u.card = s.card := Finset.card_image_of_injective s Fin.val_injective
  have hb : ∀ i ∈ u, i < C.size := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact j.isLt
  have he : ∀ i ∈ u, ∃ p < n+i, ∀ x ∈ S,
      (C.wires x).getD (n+i) false = (C.wires x).getD p false := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    exact hs j hj
  rw [← hcard]
  exact deleteMany n S hS u C hC hb he
