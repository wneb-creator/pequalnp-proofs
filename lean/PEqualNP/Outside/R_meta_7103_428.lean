import Mathlib
import PEqualNP.Defs


open Finset
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_7103_428
    (meet :
      let E := (([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map
        (fun k => ({Fin.ofNat 10 (k/10), Fin.ofNat 10 (k%10)} : Finset (Fin 10)))).toFinset
      let T := (univ : Finset (Finset (Fin 10))).filter fun s =>
        s.card = 2 ∨ s.card = 9 ∨ (∀ e ∈ E, ¬ e ⊆ s) ∧ ∀ i ∉ s, ∃ e ∈ E, e ⊆ insert i s
      let A := fun i : Fin 10 => T.filter fun s => i ∈ s
      let base := [∅, T] ++ List.ofFn A ++ [A 0 ∪ A 1]
      let goal := T.filter fun s => ∃ e ∈ E, e ⊆ s
      ∀ L : List (Finset (Finset (Fin 10))), 8 ≤ L.length → L.length ≤ 17 →
        (∀ j : Fin L.length, let W := base ++ L.take j.val
          ∃ a ∈ W, ∃ b ∈ W, L.get j = a ∩ b ∨ L.get j = a ∪ b) →
        (∀ i j : Fin 10, i ≠ j → {i,j} ∉ E → A i ∩ A j ∉ L) →
        ∀ a ∈ base ++ L, ∀ b ∈ base ++ L, a ∩ b ≠ goal)
    (join :
      let E := (([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map
        (fun k => ({Fin.ofNat 10 (k/10), Fin.ofNat 10 (k%10)} : Finset (Fin 10)))).toFinset
      let T := (univ : Finset (Finset (Fin 10))).filter fun s =>
        s.card = 2 ∨ s.card = 9 ∨ (∀ e ∈ E, ¬ e ⊆ s) ∧ ∀ i ∉ s, ∃ e ∈ E, e ⊆ insert i s
      let A := fun i : Fin 10 => T.filter fun s => i ∈ s
      let base := [∅, T] ++ List.ofFn A ++ [A 0 ∪ A 1]
      let goal := T.filter fun s => ∃ e ∈ E, e ⊆ s
      ∀ L : List (Finset (Finset (Fin 10))), 8 ≤ L.length → L.length ≤ 17 →
        (∀ j : Fin L.length, let W := base ++ L.take j.val
          ∃ a ∈ W, ∃ b ∈ W, L.get j = a ∩ b ∨ L.get j = a ∪ b) →
        (∀ i j : Fin 10, i ≠ j → {i,j} ∉ E → A i ∩ A j ∉ L) →
        ∀ a ∈ base ++ L, ∀ b ∈ base ++ L, a ∪ b ≠ goal) :
    (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → ¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  let petersenEdges : List ((Fin 10) × (Fin 10)) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let target : ((Fin 10 → Bool) → Bool) := fun x => petersenEdges.any fun e => x e.1 && x e.2
  let seed : ((Fin 10 → Bool) → Bool) := fun x => x 0 || x 1
  let start : List ((Fin 10 → Bool) → Bool) := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun i : (Fin 10) => fun x : (Fin 10 → Bool) => x i)) ++ [seed]
  let other (i : (Fin 10)) : (Fin 10) := ![4,2,1,2,0,0,1,2,3,4] i
  let lo (i : (Fin 10)) : (Fin 10 → Bool) := fun j => decide (j = other i ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0))
  let hi (i : (Fin 10)) : (Fin 10 → Bool) := fun j => (lo i j || decide (j = i))
  let sees (f : ((Fin 10 → Bool) → Bool)) (i : (Fin 10)) : Prop := f (lo i) ≠ f (hi i)
  let mono (c : (Fin 10) → (Fin 10)) (f : ((Fin 10 → Bool) → Bool)) : Prop := ∃ a, ∀ i, sees f i → c i = a
  let build (A L : List ((Fin 10 → Bool) → Bool)) : Prop := ∀ j : Fin L.length, ∃ p ∈ A ++ L.take j.val, ∃ q ∈ A ++ L.take j.val,
    (L.get j = fun x => p x && q x) ∨ L.get j = fun x => p x || q x
  have startMono : ∀ f ∈ start, mono id f := by
    intro f hf
    simp only [start,List.mem_append,List.mem_cons,List.mem_ofFn,List.not_mem_nil,or_false] at hf
    rcases hf with (rfl | rfl | ⟨j,rfl⟩) | rfl
    · exact ⟨0, fun i h => (h rfl).elim⟩
    · exact ⟨0, fun i h => (h rfl).elim⟩
    · exact ⟨j, fun i h => by
        by_contra contra
        change i ≠ j at contra
        exact h (by simp [hi,Ne.symm contra])⟩
    · exact ⟨0, fun i h => False.elim (h (by clear h; revert i; decide))⟩
  have targetSees : ∀ i, sees target i := by unfold sees; decide
  have recolor {c : (Fin 10) → (Fin 10)} (a b : (Fin 10)) :
      (Finset.univ.image c).card ≤ (Finset.univ.image (fun i => if c i = a then b else c i)).card + 1 := by
    classical
    calc
      _ ≤ (insert a (Finset.univ.image (fun i => if c i = a then b else c i))).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
        by_cases h : c i = a
        · simp [h]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,by simp [h]⟩)
      _ ≤ _ := Finset.card_insert_le ..
  have grow (A L : List ((Fin 10 → Bool) → Bool)) (c : (Fin 10) → (Fin 10)) (init : ∀ f ∈ A, mono c f) (B : build A L) :
      ∃ d : (Fin 10) → (Fin 10), (Finset.univ.image c).card ≤ (Finset.univ.image d).card + L.length ∧
        ∀ f ∈ A ++ L, mono d f := by
    induction L generalizing A c with
    | nil => exact ⟨c,by simp,by simpa using init⟩
    | cons g L ih =>
      obtain ⟨p,hp,q,hq,op⟩ := B ⟨0,by simp⟩
      simp at hp hq op
      obtain ⟨a,ha⟩ := init p hp
      obtain ⟨b,hb⟩ := init q hq
      let d := fun i => if c i = a then b else c i
      have nextB : build (A ++ [g]) L := by
        intro j
        simpa [List.append_assoc] using B j.succ
      have nextM : ∀ f ∈ A ++ [g], mono d f := by
        intro f hf
        rcases List.mem_append.mp hf with old | new
        · obtain ⟨v,hv⟩ := init f old
          exact ⟨if v = a then b else v, fun i hi => by simp [d,hv i hi]⟩
        · have eq : f = g := by simpa using new
          subst f
          refine ⟨b,fun i hi => ?_⟩
          have hpq : sees p i ∨ sees q i := by
            by_contra! nh
            apply hi
            rcases op with h|h <;> rw [h] <;> simp only [not_ne_iff,sees] at nh <;> simp [nh.1,nh.2]
          rcases hpq with h|h
          · simp [d,ha i h]
          · simp [d,hb i h]
      obtain ⟨e,card,rest⟩ := ih (A ++ [g]) d nextM nextB
      refine ⟨e,?_,by simpa [List.append_assoc] using rest⟩
      have h1 := recolor (c:=c) a b
      change (Finset.univ.image c).card ≤ (Finset.univ.image d).card + 1 at h1
      simp only [List.length_cons]
      omega
  have nine (L : List ((Fin 10 → Bool) → Bool)) (B : build start L) (h : target ∈ L) : 9 ≤ L.length := by
    obtain ⟨d,card,rest⟩ := grow start L id startMono B
    obtain ⟨v,hv⟩ := rest target (List.mem_append_right _ h)
    have hd : d = fun _ => v := funext fun i => hv i (targetSees i)
    have eq : Finset.univ.image d = {v} := by ext i; simp [hd,eq_comm]
    rw [eq] at card
    simp at card
    omega
  classical
  intro E0 L length make clean contains
  let W := (Fin 10 → Bool) → Bool
  let edges : List (Fin 10 × Fin 10) := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).map
    fun k => (Fin.ofNat 10 (k/10), Fin.ofNat 10 (k%10))
  have e0 : E0 = edges := rfl
  subst E0
  let E := (edges.map fun p => ({p.1,p.2} : Finset (Fin 10))).toFinset
  let T := (univ : Finset (Finset (Fin 10))).filter fun s => s.card = 2 ∨ s.card = 9 ∨ (∀ e ∈ E, ¬ e ⊆ s) ∧ ∀ i ∉ s, ∃ e ∈ E, e ⊆ insert i s
  let A := fun i : Fin 10 => T.filter fun s => i ∈ s
  let B : List W := [fun _ => false, fun _ => true] ++ List.ofFn (fun i x => x i) ++ [fun x => x 0 || x 1]
  let P := fun (f : W) => T.filter fun s => f (fun i => decide (i ∈ s)) = true
  let base := [∅, T] ++ List.ofFn A ++ [A 0 ∪ A 1]
  let goal := T.filter fun s => ∃ e ∈ E, e ⊆ s
  let f : W := fun x => edges.any fun p => x p.1 && x p.2
  change f ∈ L at contains
  have pAnd (a b : W) : P (fun x => a x && b x) = P a ∩ P b := by ext s; simp [P, and_assoc, and_left_comm, and_comm]
  have pOr (a b : W) : P (fun x => a x || b x) = P a ∪ P b := by ext s; simp [P, and_or_left]
  have pvar (i : Fin 10) : P (fun x => x i) = A i := by simp [P,A]
  have pbase : B.map P = base := by
    simp [B,base,P,A]
    ext s
    simp [and_or_left]
  have pgoal : P f = goal := by
    ext s
    simp [f,P,goal,E,Finset.subset_iff, Bool.and_eq_true]
  let mono (g : W) := ∀ s t : Finset (Fin 10), s ⊆ t →
    g (fun i => decide (i ∈ s)) = true → g (fun i => decide (i ∈ t)) = true
  have mbase : ∀ g ∈ B, mono g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl <;> simp [mono]
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
        intro s t h; simpa using @h i
    · simp only [List.mem_singleton] at h
      subst g
      intro s t h; simp; exact fun h' => h'.elim (fun h0 => Or.inl (h h0)) (fun h1 => Or.inr (h h1))
  have mget (j : ℕ) (hj : j < L.length) : mono L[j] := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      obtain ⟨_, a, ha, b, hb, hop⟩ := make ⟨j,hj⟩
      have prev (c : W) (hc : c ∈ B ++ L.take j) : mono c := by
        rcases List.mem_append.mp hc with h | h
        · exact mbase c h
        · obtain ⟨k,hk,eq⟩ := List.getElem_of_mem h
          rw [← eq, List.getElem_take]
          exact ih k (by have := List.length_take_le j L; omega) (by have := List.length_take_le' j L; omega)
      have ma := prev a ha
      have mb := prev b hb
      intro s t hst hval
      change L[j] = _ ∨ L[j] = _ at hop
      rcases hop with h | h <;> rw [h] at hval ⊢
      · exact Bool.and_eq_true_iff.mpr ⟨ma _ _ hst (Bool.and_eq_true_iff.mp hval).1,mb _ _ hst (Bool.and_eq_true_iff.mp hval).2⟩
      · exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp hval).elim (fun h => Or.inl (ma _ _ hst h)) (fun h => Or.inr (mb _ _ hst h)))
  have mlist (g : W) (hg : g ∈ L) : mono g := by
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    exact mget j hj
  have pclean (i j : Fin 10) (hij : i ≠ j) (hn : ({i,j} : Finset (Fin 10)) ∉ E)
      (g : W) (hg : g ∈ L) : P g ≠ A i ∩ A j := by
    intro eq
    have he : ¬(edges.any fun p => decide ((i,j) = p ∨ (j,i) = p)) = true := by
      simp only [List.any_eq_true, decide_eq_true_eq, not_exists]
      rintro p ⟨hp, rfl | rfl⟩ <;> apply hn <;> apply List.mem_toFinset.mpr <;> apply List.mem_map.mpr
      · exact ⟨_, hp, rfl⟩
      · exact ⟨_, hp, Finset.pair_comm _ _⟩
    apply clean g hg i j hij he
    have sampled (s : Finset (Fin 10)) (hs : s ∈ T) :
        g (fun k => decide (k ∈ s)) = true ↔ i ∈ s ∧ j ∈ s := by
      have h := Finset.ext_iff.mp eq s
      simpa [P,A,hs] using h
    have hpair : ({i,j} : Finset (Fin 10)) ∈ T := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Or.inl (by simp [hij])⟩
    have hco (k : Fin 10) : (univ.erase k : Finset (Fin 10)) ∈ T := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, Or.inr (Or.inl (by simp))⟩
    funext x
    let s := univ.filter fun i : Fin 10 => x i = true
    have hx : (fun i => decide (i ∈ s)) = x := by funext i; simp [s]
    rw [← hx]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    constructor
    · intro hgS
      have present (k : Fin 10) (hk : k = i ∨ k = j) : k ∈ s := by
        by_contra hn
        have hh := mlist g hg s (univ.erase k) (by intro v hv; simp; exact fun h => hn (h ▸ hv)) hgS
        have both := (sampled _ (hco k)).mp hh
        rcases hk with rfl | rfl <;> simp at both
      exact ⟨present i (Or.inl rfl),present j (Or.inr rfl)⟩
    · rintro ⟨hi,hj⟩
      exact mlist g hg {i,j} s (Finset.insert_subset_iff.mpr ⟨hi,Finset.singleton_subset_iff.mpr hj⟩) ((sampled _ hpair).mpr (by simp))
  obtain ⟨j,hj,hf⟩ := List.getElem_of_mem contains
  let M := (L.take j).map P
  have hlen : M.length ≤ 17 := by simp [M]; omega

  let K := L.take (j+1)
  have kj : K.length = j+1 := by simp [K,Nat.min_eq_left (by omega : j+1 ≤ L.length)]
  have bK : build start K := by
    intro i
    have hk := i.isLt
    have hi : i.val < L.length := by omega
    simpa only [start,seed,K,List.take_take,Nat.min_eq_left (show i.val ≤ j+1 by omega),
      List.get_eq_getElem,List.getElem_take] using (make ⟨i.val,hi⟩).2
  have hm : target ∈ K := by
    have ej : K[j]'(by omega) = target := by simpa only [K,List.getElem_take] using hf.trans (show f = target from rfl)
    exact ej ▸ List.getElem_mem (l:=K) (n:=j) (by omega)
  have nK := nine K bK hm
  have hmin : 8 ≤ M.length := by simp [M,Nat.min_eq_left (show j ≤ L.length by omega)]; omega
  have gen (k : Fin M.length) : let S := base ++ M.take k.val
        ∃ a ∈ S, ∃ b ∈ S, M.get k = a ∩ b ∨ M.get k = a ∪ b := by
    have hk := k.isLt
    simp [M] at hk
    obtain ⟨_,a,ha,b,hb,hop⟩ := make ⟨k.val,by omega⟩
    have prev (c : W) (hc : c ∈ B ++ L.take k.val) : P c ∈ base ++ M.take k.val := by
      have hh := List.mem_map_of_mem (f := P) hc
      simpa [List.map_append, pbase, M, ← List.map_take, List.take_take, Nat.min_eq_left (show k.val ≤ j by omega)] using hh
    refine ⟨P a,prev a ha,P b,prev b hb,?_⟩
    have hval : M.get k = P L[k.val] := by simp [M,List.get_eq_getElem]
    rw [hval]
    rcases hop with h | h
    · exact Or.inl ((congrArg P h).trans (pAnd a b))
    · exact Or.inr ((congrArg P h).trans (pOr a b))
  have safe (i k : Fin 10) (h : i ≠ k) (h' : ({i,k} : Finset (Fin 10)) ∉ E) :
      A i ∩ A k ∉ M := by
    intro hm
    obtain ⟨g,hg,eq⟩ := List.mem_map.mp hm
    exact pclean i k h h' g (List.mem_of_mem_take hg) eq
  obtain ⟨_,a,ha,b,hb,hop⟩ := make ⟨j,hj⟩
  have prev (c : W) (hc : c ∈ B ++ L.take j) : P c ∈ base ++ M := by
    have hh := List.mem_map_of_mem (f := P) hc
    simpa [List.map_append, pbase, M] using hh
  rcases hop with h | h
  · apply meet M hmin hlen gen safe (P a) (prev a ha) (P b) (prev b hb)
    exact (pAnd a b).symm.trans ((congrArg P h).symm.trans ((congrArg P hf).trans pgoal))
  · apply join M hmin hlen gen safe (P a) (prev a ha) (P b) (prev b hb)
    exact (pOr a b).symm.trans ((congrArg P h).symm.trans ((congrArg P hf).trans pgoal))
