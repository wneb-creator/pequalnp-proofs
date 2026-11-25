import Structural16

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

lemma from_constant_comb {R u} {bank : List (Wire R)} {d a b}
    (hd : allowed u d) (hc : Constant a ∨ Constant b)
    (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · exact from_constant false hc ha hb
  · exact from_constant true hc ha hb
  · exact from_constant false (hc.imp id inv_constant) ha (avail_inv hu hb)
  · exact from_constant false (hc.imp inv_constant id) (avail_inv hu ha) hb

lemma mass_retained_constant {R} (z a b : Wire R) (rest : List (Wire R))
    (ka kb : Bool) (hc : (Constant a ∧ ka = true) ∨ (Constant b ∧ kb = true)) :
    1 ≤ mass (z :: kept ka a (kept kb b rest)) := by
  classical
  rcases hc with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
  · simp [kept, mass_cons, cost, ha]
    omega
  · have hk := mass_kept a (kept true b rest) ka
    simp only [kept, ite_true, mass_cons] at hk ⊢
    have hcost : cost b = 1 := by simp [cost, hb]
    omega

lemma projected_bound_retained {R S : Type} {u} (rows : S → R)
    {goal : Wire R} {s d ka kb a b rest} (hd : allowed u d)
    (tail : Run u goal s (comb d a b :: kept ka a (kept kb b rest)))
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank)
    (hs : supply u bank ((a :: b :: rest).map (restrictRows rows)))
    (hc : (Constant (restrictRows rows a) ∧ ka = true) ∨
      (Constant (restrictRows rows b) ∧ kb = true))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + 2 ≤ p + (s + 1) := by
  have hca : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b) :=
    hc.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have havA := hs (restrictRows rows a) (by simp)
  have havB := hs (restrictRows rows b) (by simp)
  have havG := from_constant_comb hd hca havA havB
  have hsTail : supply u bank
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept, restrict_comb]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact havG
    · rcases mem_kept hv with rfl | hv
      · exact havA
      · rcases mem_kept hv with rfl | hv
        · exact havB
        · exact hs v (by simp [hv])
  have bound := projected_bound rows tail nc hp hsTail hl
  have charged : 1 ≤ mass
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept, restrict_comb]
    exact mass_retained_constant _ _ _ _ _ _ hc
  omega

lemma projected_bound_retained_result {R S : Type} {u} (rows : S → R)
    {goal : Wire R} {s d ka kb a b rest} (hd : allowed u d)
    (tail : Run u goal s (comb d a b :: kept ka a (kept kb b rest)))
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank)
    (hs : supply u bank ((a :: b :: rest).map (restrictRows rows)))
    (hc : (Constant (restrictRows rows a) ∧ ka = true) ∨
      (Constant (restrictRows rows b) ∧ kb = true))
    (hresult : Constant (restrictRows rows (comb d a b)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + 3 ≤ p + (s + 1) := by
  classical
  have hsTail : supply u bank
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inr (Or.inl hresult)
    · rcases mem_kept hv with rfl | hv
      · exact hs _ (by simp)
      · rcases mem_kept hv with rfl | hv
        · exact hs _ (by simp)
        · exact hs v (by simp [hv])
  have bound := projected_bound rows tail nc hp hsTail hl
  have charged : 2 ≤ mass
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept]
    rcases hc with ⟨ha, hka⟩ | ⟨hb, hkb⟩
    · simp only [hka, kept, ite_true, mass_cons]
      simp only [cost, if_pos hresult, if_pos ha]
      omega
    · have hk := mass_kept (restrictRows rows a)
        (kept true (restrictRows rows b) (rest.map (restrictRows rows))) ka
      simp only [hkb, kept, ite_true, mass_cons] at hk ⊢
      have hbCost : cost (restrictRows rows b) = 1 := by simp [cost, hb]
      have hrCost : cost (restrictRows rows (comb d a b)) = 1 := by simp [cost, hresult]
      omega
  omega

def rowPermutations : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
   [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
   [4, 3, 2, 1, 0, 9, 8, 7, 6, 5],
   [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
   [3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
   [6, 1, 0, 4, 9, 8, 2, 5, 3, 7],
   [1, 6, 9, 4, 0, 2, 8, 7, 3, 5],
   [9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
   [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
   [4, 9, 6, 1, 0, 3, 7, 8, 2, 5]]

def rowsFor (j : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((List.range 10).map fun b =>
    if r.val.testBit ((rowPermutations.getD j.val []).getD b 0) then 2 ^ b else 0).sum

def projectFor (j : Fin 10) (a : Extended.Sig) : Sig :=
  table (restrictRows (rowsFor j) (Extended.observe a))

lemma observe_projectFor (j : Fin 10) (a : Extended.Sig) :
    restrictRows (rowsFor j) (Extended.observe a) = observe (projectFor j a) :=
  (observe_table _).symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma projectFor_target : ∀ j : Fin 10, projectFor j Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma projectFor_pin : ∀ j : Fin 10,
    projectFor j (Extended.pins.getD j.val Extended.zero) = zero := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma projectFor_permitted : ∀ j : Fin 10,
    Extended.pins.all (fun a => (projectFor j a == zero) || inputs.contains (projectFor j a)) = true := by
  decide +kernel

lemma restriction_of_pin_is_available (j : Fin 10) (a : Extended.Sig)
    (ha : a ∈ Extended.pins) :
    Available true (inputs.map observe) (restrictRows (rowsFor j) (Extended.observe a)) := by
  rw [observe_projectFor]
  have permitted := List.all_eq_true.mp (projectFor_permitted j) a ha
  simp only [Bool.or_eq_true, beq_iff_eq] at permitted
  rcases permitted with hz | hm
  · right; left
    refine ⟨false, ?_⟩
    rw [hz]
    funext r
    simp [observe, bit, zero]
  · left
    exact List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩

lemma pin_index (a : Extended.Sig) (ha : a ∈ Extended.pins) :
    ∃ j : Fin 10, Extended.pins.getD j.val Extended.zero = a := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  have ilt : i.val < 10 := by simpa [Extended.pins] using i.isLt
  refine ⟨⟨i.val, ilt⟩, ?_⟩
  simpa [List.getD_eq_getElem?_getD, i.isLt] using hi

lemma restriction_of_selected_pin (j : Fin 10) :
    Constant (restrictRows (rowsFor j)
      (Extended.observe (Extended.pins.getD j.val Extended.zero))) := by
  rw [observe_projectFor, projectFor_pin]
  refine ⟨false, ?_⟩
  funext r
  simp [observe, bit, zero]

lemma restriction_of_goal (j : Fin 10) :
    restrictRows (rowsFor j) (Extended.observe Extended.target) = observe graph := by
  rw [observe_projectFor, projectFor_target]

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
