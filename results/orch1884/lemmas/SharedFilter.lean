import PairLocalization

namespace PEqualNP.Outside.L_meta_1884.SharedFilter

open Finset SoleOrPartner

def point (S : Finset (Fin 10)) : Fin 10 → Bool := fun i => decide (i ∈ S)

def fiberMono (H : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 10 → Bool, x 0 = y 0 →
    (∀ i, x i = true → y i = true) → H x = true → H y = true

def independent (v : Fin 10) (H : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) → H x = H y

def factor (v : Fin 10) (H : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
    (x v || H x) = (y v || H y) → target x = target y

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
lemma negative_card : ∀ S : Finset (Fin 10), target (point S) = false → S.card ≤ 4 := by
  decide

lemma negative_subset (S T : Finset (Fin 10)) (hst : S ⊆ T)
    (ht : target (point T) = false) : target (point S) = false := by
  simp only [target, point, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, and_assoc] at ht ⊢
  rcases ht with ⟨h01, h12, h23, h34, h40, h05, h16, h27, h38, h49,
    h57, h79, h96, h68, h85⟩
  have lift (a b : Fin 10) (h : a ∉ T ∨ b ∉ T) : a ∉ S ∨ b ∉ S :=
    h.imp (fun hn hs => hn (hst hs)) (fun hn hs => hn (hst hs))
  exact ⟨lift _ _ h01, lift _ _ h12, lift _ _ h23, lift _ _ h34, lift _ _ h40,
    lift _ _ h05, lift _ _ h16, lift _ _ h27, lift _ _ h38, lift _ _ h49,
    lift _ _ h57, lift _ _ h79, lift _ _ h96, lift _ _ h68, lift _ _ h85⟩

lemma maximal_extension (S : Finset (Fin 10)) (hs : target (point S) = false) :
    ∃ T : Finset (Fin 10), S ⊆ T ∧ point T 0 = point S 0 ∧
      target (point T) = false ∧
      ∀ v : Fin 10, v ≠ 0 → v ∉ T → target (point (insert v T)) = true := by
  classical
  let candidates := univ.filter (fun T : Finset (Fin 10) =>
    S ⊆ T ∧ point T 0 = point S 0 ∧ target (point T) = false)
  have hn : candidates.Nonempty := ⟨S, by simp [candidates, hs]⟩
  obtain ⟨T, hT, hmax⟩ := exists_max_image candidates Finset.card hn
  have hspec : S ⊆ T ∧ point T 0 = point S 0 ∧ target (point T) = false :=
    (mem_filter.mp hT).2
  refine ⟨T, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  intro v hv0 hnv
  cases hv : target (point (insert v T))
  · have hi : insert v T ∈ candidates := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, hspec.1.trans (subset_insert _ _), ?_, hv⟩
      simpa [point, Ne.symm hv0] using hspec.2.1
    have hcard := hmax (insert v T) hi
    rw [card_insert_of_notMem hnv] at hcard
    omega
  · rfl

lemma forced_member (v : Fin 10) (hv0 : v ≠ 0) (H : (Fin 10 → Bool) → Bool)
    (hf : factor v H) (T : Finset (Fin 10)) (ht : target (point T) = false)
    (hh : H (point T) = true)
    (hmax : ∀ v : Fin 10, v ≠ 0 → v ∉ T → target (point (insert v T)) = true) :
    v ∈ T := by
  by_contra hn
  have hp := hmax v hv0 hn
  have heq := hf (point T) (point (insert v T))
    (by intro i hi; simp [point, hi])
    (by simp [point, hh])
  rw [ht, hp] at heq
  cases heq

lemma erase_irrelevant (v : Fin 10) (H : (Fin 10 → Bool) → Bool)
    (hi : independent v H) (T : Finset (Fin 10)) :
    H (point (T.erase v)) = H (point T) := by
  apply hi
  intro i hiv
  simp [point, hiv]

theorem unsafe_pair (v w : Fin 10) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (H : (Fin 10 → Bool) → Bool) (hm : fiberMono H)
    (hiv : independent v H) (hiw : independent w H)
    (hfv : factor v H) (hfw : factor w H)
    (S : Finset (Fin 10)) (hs : target (point S) = false) (hh : H (point S) = true) :
    ∃ a b : Fin 10, target (pair a b) = false ∧ H (pair a b) = true ∧
      exceptional v a b ∧ exceptional w a b := by
  classical
  obtain ⟨T, hst, hzero, ht, hmax⟩ := maximal_extension S hs
  have hH : H (point T) = true := hm _ _ hzero.symm
    (by intro i hi; simp only [point, decide_eq_true_eq] at hi ⊢; exact hst hi) hh
  have hv := forced_member v hv0 H hfv T ht hH hmax
  have hw := forced_member w hw0 H hfw T ht hH hmax
  let U := (T.erase v).erase w
  have hHu : H (point U) = true := by
    rw [show H (point U) = H (point (T.erase v)) from erase_irrelevant w H hiw _,
      erase_irrelevant v H hiv T]
    exact hH
  have hsub : U ⊆ T := (erase_subset _ _).trans (erase_subset _ _)
  have hneg : target (point U) = false := negative_subset U T hsub ht
  have hcard : U.card ≤ 2 := by
    have hct := negative_card T ht
    have hw' : w ∈ T.erase v := mem_erase.mpr ⟨Ne.symm hvw, hw⟩
    dsimp only [U]
    rw [card_erase_of_mem hw', card_erase_of_mem hv]
    omega
  have hc2 : U.card = 2 := by
    have hn0 : U.card ≠ 0 := by
      intro hz
      have he : U = ∅ := card_eq_zero.mp hz
      have hp : point U = (fun _ => false) := by funext i; simp [he, point]
      rw [hp, rejects_zero v hv0 H hm hfv] at hHu
      cases hHu
    have hn1 : U.card ≠ 1 := by
      intro ho
      obtain ⟨a, ha⟩ := card_eq_one.mp ho
      have hp : point U = SoleOrPartner.singleton a := by
        funext i
        simp [ha, point, SoleOrPartner.singleton]
      rw [hp, rejects_singleton v hv0 H hm hiv hfv a] at hHu
      cases hHu
    omega
  obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp hc2
  have hp : point U = pair a b := by funext i; simp [heq, point, pair]
  rw [hp] at hneg hHu
  exact ⟨a, b, hneg, hHu,
    localizes_nonedge_pair v hv0 H hm hiv hfv a b hneg hHu,
    localizes_nonedge_pair w hw0 H hm hiw hfw a b hneg hHu⟩

end PEqualNP.Outside.L_meta_1884.SharedFilter
