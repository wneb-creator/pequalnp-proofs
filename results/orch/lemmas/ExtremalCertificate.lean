import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650.Certificate

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma quad : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter (fun y : Fin 13 =>
      (a.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (b.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      (c.val + y.val) % 13 ∉ [0, 1, 3, 9] ∧ (d.val + y.val) % 13 ∉ [0, 1, 3, 9])).card ≤ 3 := by
  decide +kernel


lemma geometry : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, (↑x3 + ↑x5) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro A B h
  by_contra hcon
  push_neg at hcon
  have h4 : 4 ≤ A.card := by omega
  have hmem : ∀ i : Fin 4, A.orderEmbOfCardLe h4 i ∈ A := fun i => Finset.orderEmbOfCardLe_mem A h4 i
  have hmono := (A.orderEmbOfCardLe h4).strictMono
  have hq := quad (A.orderEmbOfCardLe h4 0) (A.orderEmbOfCardLe h4 1)
    (A.orderEmbOfCardLe h4 2) (A.orderEmbOfCardLe h4 3)
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
  have hsub : B ⊆ Finset.univ.filter (fun y : Fin 13 =>
      ((A.orderEmbOfCardLe h4 0).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 1).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 2).val + y.val) % 13 ∉ [0, 1, 3, 9] ∧
      ((A.orderEmbOfCardLe h4 3).val + y.val) % 13 ∉ [0, 1, 3, 9]) := by
    intro y hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h _ (hmem 0) y hy, h _ (hmem 1) y hy, h _ (hmem 2) y hy,
      h _ (hmem 3) y hy⟩
  have := Finset.card_le_card hsub
  omega

def Tests (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ s)
    else decide ((Fin.ofNat 13 i.val) ∈ t)
  let off := fun (s : Finset (Fin 13)) =>
    Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let read := fun s t => C.eval (List.ofFn (vec s t))
  (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 →
      read s (off s) = false ∧ read (off s) s = false)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
lemma sufficient (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (size : C.size ≤ 63)
    (tests : Tests C) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ s) else decide ((Fin.ofNat 13 i.val) ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let read := fun s t => C.eval (List.ofFn (vec s t))
  change (∀ p l : Fin 13, near p l → read {p} {l} = true) ∧
    (∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false) at tests
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le := fun (w z : List Bool) => ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
      (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g) (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).all id = true → (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact le i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).any id = true → (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,le i ha⟩
      intro i
      by_cases small : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)] using le i
      · have big : w.length ≤ i := by omega
        simp only [step,List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : i-w.length with
        | zero => exact gate
        | succ j => simp
  have mono {s t u v : Finset (Fin 13)} (a : s ⊆ u) (b : t ⊆ v) :
      read s t = true → read u v = true := by
    have init : Le (List.ofFn (vec s t)) (List.ofFn (vec u v)) := by
      intro j
      by_cases hj : j < 26
      · rw [List.getD_eq_getElem (List.ofFn (vec s t)) false (by simpa only [List.length_ofFn] using hj),
            List.getD_eq_getElem (List.ofFn (vec u v)) false (by simpa only [List.length_ofFn] using hj)]
        simp only [List.getElem_ofFn]
        by_cases hp : j < 13
        · simpa [vec,hp] using a (x := Fin.ofNat 13 j)
        · simpa [vec,hp] using b (x := Fin.ofNat 13 j)
      · rw [List.getD_eq_default (List.ofFn (vec s t)) false (by simp only [List.length_ofFn]; omega)]
        intro h
        exact Bool.noConfusion h
    exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp) init C.output
  let pt (p : Fin 13) : Fin 26 := ⟨p.val,by omega⟩
  let ln (l : Fin 13) : Fin 26 := ⟨13+l.val,by omega⟩
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ u v : Fin 26, (u.val,v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ near (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val) := by
    dsimp only [edges,near]
    decide +kernel
  have points : ∀ p : Fin 13, (Fin.ofNat 13 (pt p).val) = p := by
    intro p
    apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  have lines : ∀ l : Fin 13, (Fin.ofNat 13 (ln l).val) = l := by
    intro l
    apply Fin.ext
    change (13+l.val) % 13 = l.val
    omega
  have pointInv : ∀ i : Fin 26, i.val < 13 → pt (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  have lineInv : ∀ i : Fin 26, 13 ≤ i.val → ln (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    change 13+i.val % 13 = i.val
    omega
  refine ⟨C,hm,size,?_⟩
  intro x
  let s := Finset.univ.filter fun p : Fin 13 => x (pt p) = true
  let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
  have repr : vec s t = x := by
    funext i
    by_cases hi : i.val < 13
    · simp only [vec,ite_eq_left hi,s,Finset.mem_filter,Finset.mem_univ,true_and,pointInv i hi]
      simp
    · simp only [vec,ite_eq_right hi,t,Finset.mem_filter,Finset.mem_univ,true_and,lineInv i (by omega)]
      simp
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true
  have arr : (∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true) ↔
      ∃ p ∈ s, ∃ l ∈ t, near p l := by
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      obtain ⟨ha,hb,hc⟩ := (table u v).mp he
      exact ⟨Fin.ofNat 13 u.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [pointInv u ha]; exact hu⟩,Fin.ofNat 13 v.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [lineInv v hb]; exact hv⟩,hc⟩
    · rintro ⟨p,hp,l,hl,hpl⟩
      refine ⟨pt p,ln l,(table _ _).mpr ⟨by dsimp [pt]; omega,by dsimp [ln]; omega,?_⟩,?_,?_⟩
      · simpa only [points,lines] using hpl
      · simpa [s] using hp
      · simpa [t] using hl
  rw [arr,← repr]
  change read s t = true ↔ _
  constructor
  · intro accepted
    by_contra no
    have miss : ∀ p ∈ s, ∀ l ∈ t, ¬ near p l := fun p hp l hl e => no ⟨p,hp,l,hl,e⟩
    rcases geometry s t miss with sp | st
    · have sub : t ⊆ off s := by
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => miss p hp l hl⟩
      have bad := mono (Finset.Subset.rfl : s ⊆ s) sub accepted
      rw [(tests.2 s sp).1] at bad
      exact Bool.noConfusion bad
    · have sub : s ⊆ off t := by
        intro p hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro l hl
        simpa only [near,Nat.add_comm l.val p.val] using miss p hp l hl
      have bad := mono sub (Finset.Subset.rfl : t ⊆ t) accepted
      rw [(tests.2 t st).2] at bad
      exact Bool.noConfusion bad
  · rintro ⟨p,hp,l,hl,hpl⟩
    exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (tests.1 p l hpl)

end PEqualNP.Outside.L_meta_650.Certificate
