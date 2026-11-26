import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private abbrev W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  scan boolStep gs (List.ofFn x)

private theorem inputAt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (W n gs x).getD i false = x ⟨i,hi⟩ := by
  rw [scan_prefix boolStep _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem countFilterStep (S : Finset ℕ) (j : ℕ) :
    (S.filter (· < j+1)).card = (S.filter (· < j)).card + if j ∈ S then 1 else 0 := by
  by_cases hm : j ∈ S
  · have e : S.filter (· < j+1) = insert j (S.filter (· < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hl⟩
        by_cases e : i = j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [e,Finset.card_insert_of_notMem (by simp),ite_eq_left hm]
  · have e : S.filter (· < j+1) = S.filter (· < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hl⟩
        exact ⟨hi,by have hn : i ≠ j := fun eq => hm (eq ▸ hi); omega⟩
      · rintro ⟨hi,hl⟩; exact ⟨hi,by omega⟩
    rw [e,ite_eq_right hm,Nat.add_zero]

private abbrev pinned {n : ℕ} (x : Fin n → Bool) (p q : Fin n) :=
  Function.update (Function.update x p false) q false

private abbrev absent (n : ℕ) (C : Circuit) := n + C.gates.length

private def Available (n : ℕ) (C : Circuit) (gs : List Gate) (i : ℕ) : Prop :=
  i < n + gs.length ∨ i = absent n C

private def retained (n : ℕ) (T : Finset ℕ) (i : ℕ) : Prop :=
  ∀ k ∈ T, i ≠ n + k

private theorem wiresLength {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W n gs x).length = n + gs.length := by rw [scan_length,List.length_ofFn]

private theorem previousValues {n : ℕ} (L R : List Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + L.length) :
    (W n (L ++ R) x).getD i false = (W n L x).getD i false := by
  simp only [W,scan_append]
  exact scan_prefix _ _ _ _ _ (by simpa only [wiresLength] using hi)

private theorem missingValue {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : n + gs.length ≤ i) : (W n gs x).getD i false = false := by
  apply List.getD_eq_default
  rwa [wiresLength]

private theorem gatePrevious {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    (W n C.gates x).getD (n+j) false = boolStep (W n (C.gates.take j) x) C.gates[j] := by
  have leng : (C.gates.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have split : (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j+1) = C.gates := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have wpre := previousValues (C.gates.take j ++ [C.gates[j]]) (C.gates.drop (j+1))
    x (n+j) (by rw [List.length_append,List.length_singleton,leng]; omega)
  rw [split] at wpre
  rw [wpre]
  simp only [W,scan_append]
  rw [show scan boolStep [C.gates[j]] (W n (C.gates.take j) x) =
      W n (C.gates.take j) x ++ [boolStep (W n (C.gates.take j) x) C.gates[j]] from rfl]
  have lenW : (W n (C.gates.take j) x).length = n+j := by rw [wiresLength,leng]
  rw [List.getD_append_right _ _ _ _ (by rw [lenW]),lenW,Nat.sub_self,List.getD_cons_zero]

private theorem prefixRead {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j ≤ C.gates.length) {i : ℕ} (hi : i < n+j) :
    (W n (C.gates.take j) x).getD i false = (W n C.gates x).getD i false := by
  have hw := previousValues (C.gates.take j) (C.gates.drop j) x i
    (by simpa [Nat.min_eq_left hj] using hi)
  rwa [List.take_append_drop,eq_comm] at hw

private structure Prefix (n : ℕ) (C : Circuit) (p q : Fin n)
    (dropSet dead : Finset ℕ) (j : ℕ) where
  gs : List Gate
  f : ℕ → ℕ
  legal : FanInTwo (⟨gs,0⟩ : Circuit)
  cost : gs.length + (dropSet.filter (· < j)).card ≤ j
  valids : ∀ i < n+j, Available n C gs (f i)
  sound : ∀ i < n+j, retained n dead i → ∀ x : Fin n → Bool,
    (W n gs x).getD (f i) false = (W n C.gates (pinned x p q)).getD i false

private def Prefix.advance {n : ℕ} {C : Circuit} {p q : Fin n}
    {dropSet dead : Finset ℕ} {j : ℕ} (P : Prefix n C p q dropSet dead j)
    (extra : List Gate) (out : ℕ)
    (next : j+1 ≤ C.gates.length) (newLegal : FanInTwo (⟨extra,0⟩ : Circuit))
    (newCost : extra.length + (if j ∈ dropSet then 1 else 0) ≤ 1)
    (newRef : Available n C (P.gs ++ extra) out)
    (newSound : retained n dead (n+j) → ∀ x : Fin n → Bool,
      (W n (P.gs ++ extra) x).getD out false =
        (W n C.gates (pinned x p q)).getD (n+j) false) :
    Prefix n C p q dropSet dead (j+1) := by
  let gs := P.gs ++ extra
  let f (i : ℕ) := if i = n+j then out else P.f i
  have cost : gs.length + (dropSet.filter (· < j+1)).card ≤ j+1 := by
    have h := P.cost
    rw [countFilterStep]
    simp only [gs,List.length_append]
    omega
  have small : gs.length ≤ C.gates.length := by omega
  refine ⟨gs,f,?_,cost,?_,?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact P.legal g h
    · exact newLegal g h
  · intro i hi
    by_cases h : i = n+j
    · simpa [f,h] using newRef
    · simp only [f,h,ite_false]
      rcases P.valids i (by omega) with hlt | heq
      · left
        simp only [gs,List.length_append]
        omega
      · exact Or.inr heq
  · intro i hi alive x
    by_cases h : i = n+j
    · subst i
      simpa [f] using newSound alive x
    · simp only [f,h,ite_false]
      rw [← P.sound i (by omega) alive x]
      rcases P.valids i (by omega) with hlt | heq
      · exact previousValues P.gs extra x (P.f i) hlt
      · rw [heq, missingValue gs x _ (by simp only [absent]; omega), missingValue P.gs x _]
        simp only [gs,List.length_append] at small
        simp only [absent]
        omega

private theorem rawRetained {n i : ℕ} (T : Finset ℕ) (hi : i < n) :
    retained n T i := by
  intro k hk h
  omega

private def advanceReused {n : ℕ} {C : Circuit} {p q : Fin n}
    {dropSet dead : Finset ℕ} {j : ℕ} (P : Prefix n C p q dropSet dead j)
    (next : j+1 ≤ C.gates.length) (r : ℕ) (valid : Available n C P.gs r)
    (sound : retained n dead (n+j) → ∀ x : Fin n → Bool,
      (W n P.gs x).getD r false = (W n C.gates (pinned x p q)).getD (n+j) false) :
    Prefix n C p q dropSet dead (j+1) := by
  refine P.advance [] r next (by simp [FanInTwo]) ?_ ?_ ?_
  · by_cases h : j ∈ dropSet <;> simp [h]
  · simpa using valid
  · simpa using sound

private theorem build {n : ℕ} (C : Circuit) (p q : Fin n) (S T : Finset ℕ)
    (hC : FanInTwo C)
    (aliases : ∀ j ∈ S, ∃ i, (i < n+j ∨ absent n C ≤ i) ∧
      retained n T i ∧ ∀ x : Fin n → Bool,
      (W n C.gates (pinned x p q)).getD (n+j) false =
        (W n C.gates (pinned x p q)).getD i false)
    (deadUses : ∀ k ∈ T, ∀ j g, C.gates[j]? = some g →
      n+k ∈ g.inputs → j ∈ S ∪ T)
    (j : ℕ) (bound : j ≤ C.gates.length) : Nonempty (Prefix n C p q (S ∪ T) T j) := by
  induction j with
  | zero =>
    refine ⟨⟨[],fun i => if i = p.val ∨ i = q.val then absent n C else i,by simp [FanInTwo],by simp,?_,?_⟩⟩
    · intro i hi
      by_cases h : i = p.val ∨ i = q.val
      · simp [h,Available]
      · simpa [h,Available] using Or.inl (b := i = absent n C) hi
    · intro i hi _ x
      have hi' : i < n := by simpa using hi
      let k : Fin n := ⟨i,hi'⟩
      have hp : k = p ↔ i = p.val := ⟨congrArg Fin.val,fun h => Fin.ext h⟩
      have hq : k = q ↔ i = q.val := ⟨congrArg Fin.val,fun h => Fin.ext h⟩
      rw [inputAt C.gates _ i hi']
      change _ = pinned x p q k
      by_cases e : i = p.val ∨ i = q.val
      · simp only [e,ite_true]
        rw [missingValue [] x _ (by simp)]
        rcases e with he | he
        · have ep := hp.mpr he
          rw [ep]
          by_cases epq : p = q
          · simp [pinned,epq]
          · simp [pinned,Function.update_of_ne epq]
        · rw [hq.mpr he]
          simp [pinned]
      · have en := not_or.mp e
        simp only [e,ite_false]
        rw [inputAt [] x i hi']
        simp [pinned,Function.update_of_ne (mt hp.mp en.1),Function.update_of_ne (mt hq.mp en.2),k]
  | succ j ih =>
    obtain ⟨P⟩ := ih (by omega)
    have hj : j < C.gates.length := by omega
    by_cases ht : j ∈ T
    · refine ⟨advanceReused P bound (absent n C) (Or.inr rfl) (fun live => ?_)⟩
      exact False.elim (live j ht rfl)
    by_cases hs : j ∈ S
    · obtain ⟨i,hi,avail,cert⟩ := aliases j hs
      rcases hi with earlier | beyond
      · refine ⟨advanceReused P bound (P.f i) (P.valids i earlier) (fun _ x => ?_)⟩
        exact (P.sound i earlier avail x).trans (cert x).symm
      · refine ⟨advanceReused P bound (absent n C) (Or.inr rfl) (fun _ x => ?_)⟩
        rw [cert x, missingValue C.gates _ i beyond]
        exact missingValue P.gs _ _ (by have := P.cost; simp only [absent]; omega)
    · let g := C.gates[j]
      let remap (i : ℕ) := if i < n+j then P.f i else absent n C
      let g' : Gate := ⟨g.op,g.inputs.map remap⟩
      have gFan : FanInTwo (⟨[g'],0⟩ : Circuit) := by
        intro a ha
        obtain rfl := List.mem_singleton.mp ha
        have old := hC g (List.getElem_mem hj)
        simpa [g',g] using old
      have outside : j ∉ S ∪ T := by simp [hs,ht]
      refine ⟨P.advance [g'] (n+P.gs.length) bound gFan
        (by simp [outside]) (Or.inl (by simp)) (fun _ x => ?_)⟩
      simp only [W,scan_append]
      rw [show scan boolStep [g'] (W n P.gs x) =
        W n P.gs x ++ [boolStep (W n P.gs x) g'] from rfl]
      rw [← wiresLength P.gs x,List.getD_append_right _ _ _ _ (Nat.le_refl _),
        Nat.sub_self,List.getD_cons_zero,gatePrevious C (pinned x p q) j hj]
      unfold boolStep
      simp only [g',List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hm
      change (W n P.gs x).getD (remap i) false =
        (W n (C.gates.take j) (pinned x p q)).getD i false
      by_cases hlt : i < n+j
      · have live : retained n T i := by
          intro k hk e
          apply outside
          exact deadUses k hk j g (List.getElem?_eq_getElem hj) (e ▸ hm)
        rw [show remap i = P.f i by simp [remap,hlt],P.sound _ hlt live,
          prefixRead C _ j (by omega) hlt]
      · rw [show remap i = absent n C by simp [remap,hlt]]
        rw [missingValue P.gs x _ (by have := P.cost; simp only [absent]; omega),missingValue]
        simp only [List.length_take,Nat.min_eq_left hj.le]
        omega

end PEqualNP.Outside.L_meta_18159

theorem PEqualNP.Outside.L_meta_18159 :
  ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 x6 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     Disjoint x5 x6 →       (∀ x9 ∈ x5, x9 < x2.size) →         (∀ x10 ∈ x6, x10 < x2.size) →           (∀ x11 ∈ x5,               ∃ (x13 : ℕ),                 (x13 < x1 + x11 ∨ x1 + x2.size ≤ x13) ∧                   (∀ x14 ∈ x6, x13 ≠ x1 + x14) ∧                     ∀ (x14 : Fin x1 → Bool),                       have x15 : List Bool := x2.wires (List.ofFn (Function.update (Function.update x14 x3 Bool.false) x4 Bool.false));                       x15.getD (x1 + x11) Bool.false = x15.getD x13 Bool.false) →             (∀ x12 ∈ x6, x2.output ≠ x1 + x12 ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x14]? = Option.some x15 → x1 + x12 ∈ x15.inputs → x14 ∈ x5 ∪ x6) → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x13 x3 Bool.false) x4 Bool.false))) (x2.size - x5.card - x6.card) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18159 in
  intro n C p q S T hC dj hS hT al dead
  obtain ⟨P⟩ := build C p q S T hC al (fun k hk j g e m => (dead k hk).2 j g e m)
    C.gates.length (Nat.le_refl _)
  have unionAll : (S ∪ T).filter (· < C.gates.length) = S ∪ T := by
    apply Finset.filter_true_of_mem
    intro k hk
    rcases Finset.mem_union.mp hk with a | b
    · exact hS k a
    · exact hT k b
  have enough := P.cost
  rw [unionAll,Finset.card_union_of_disjoint dj] at enough
  let out := if C.output < n+C.gates.length then P.f C.output else absent n C
  refine ⟨⟨P.gs,out⟩,P.legal,by change P.gs.length ≤ _; change _ ≤ C.gates.length - _ - _; omega,?_⟩
  intro x
  change (W n P.gs x).getD out false = (W n C.gates (pinned x p q)).getD C.output false
  by_cases ho : C.output < n+C.gates.length
  · have live : retained n T C.output := fun k hk => (dead k hk).1
    simpa [out,ho] using P.sound C.output ho live x
  · simp only [out,ho,ite_false]
    rw [missingValue P.gs x _ (by simp only [absent]; omega),missingValue C.gates _ _ (by omega)]
