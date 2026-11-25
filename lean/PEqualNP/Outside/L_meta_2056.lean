import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2056_aux

abbrev incident (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def neighbors (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (incident p)

def incidences : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => incident e.1 e.2

lemma incident_symmetric (p l : Fin 13) : incident p l ↔ incident l p := by
  simp only [incident, Nat.add_comm]

lemma neighbors_card : ∀ p : Fin 13, (neighbors p).card = 4 := by
  decide +kernel

lemma incidences_card : incidences.card = 52 := by
  decide +kernel

lemma no_rectangle : ∀ a b c d : Fin 13,
    a ≠ b → c ≠ d → incident a c → incident a d → incident b c → ¬ incident b d := by
  decide +kernel

lemma unique_common_neighbor : ∀ a b : Fin 13, a ≠ b →
    ∃! l : Fin 13, incident a l ∧ incident b l := by
  unfold ExistsUnique
  decide +kernel



open scoped BigOperators

lemma rectangle_star (s t : Finset (Fin 13))
    (h : ∀ p ∈ s, ∀ l ∈ t, incident p l) : s.card ≤ 1 ∨ t.card ≤ 1 := by
  by_cases hs : s.card ≤ 1
  · exact Or.inl hs
  right
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  obtain ⟨b, hb, hab⟩ := s.exists_mem_ne (by omega) a
  apply Finset.card_le_one.mpr
  intro c hc d hd
  by_contra hcd
  exact no_rectangle a b c d hab.symm hcd (h a ha c hc) (h a ha d hd)
    (h b hb c hc) (h b hb d hd)

lemma rectangle_sides_le_four (s t : Finset (Fin 13))
    (hs : s.Nonempty) (ht : t.Nonempty)
    (h : ∀ p ∈ s, ∀ l ∈ t, incident p l) : s.card ≤ 4 ∧ t.card ≤ 4 := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := ht
  constructor
  · calc
      s.card ≤ (neighbors b).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (incident_symmetric p b).mp (h p hp b hb)⟩)
      _ = 4 := neighbors_card b
  · calc
      t.card ≤ (neighbors a).card := Finset.card_le_card (by
        intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h a ha l hl⟩)
      _ = 4 := neighbors_card a

lemma rectangle_count (s t : Finset (Fin 13))
    (hs : s.Nonempty) (ht : t.Nonempty)
    (h : ∀ p ∈ s, ∀ l ∈ t, incident p l) :
    s.card * t.card ≤ 4 ∧ s.card + t.card = s.card * t.card + 1 := by
  have hsp := hs.card_pos
  have htp := ht.card_pos
  obtain ⟨hs4, ht4⟩ := rectangle_sides_le_four s t hs ht h
  rcases rectangle_star s t h with hs1 | ht1
  · have he : s.card = 1 := by omega
    rw [he, Nat.one_mul]
    exact ⟨ht4, Nat.add_comm 1 _⟩
  · have he : t.card = 1 := by omega
    rw [he, Nat.mul_one]
    exact ⟨hs4, rfl⟩

lemma rectangle_cover_cost (m : ℕ) (s t : Fin m → Finset (Fin 13))
    (hs : ∀ i, (s i).Nonempty) (ht : ∀ i, (t i).Nonempty)
    (hrect : ∀ i p, p ∈ s i → ∀ l, l ∈ t i → incident p l)
    (hcover : ∀ p l, incident p l → ∃ i, p ∈ s i ∧ l ∈ t i) :
    13 ≤ m ∧ 64 ≤ (∑ i, ((s i).card + (t i).card)) - 1 := by
  have hsub : incidences ⊆ Finset.univ.biUnion (fun i => (s i).product (t i)) := by
    intro e he
    obtain ⟨i, hp, hl⟩ := hcover e.1 e.2 (show incident e.1 e.2 from (Finset.mem_filter.mp he).2)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨hp, hl⟩⟩
  have h52 : 52 ≤ ∑ i, (s i).card * (t i).card := by
    calc
      52 = incidences.card := incidences_card.symm
      _ ≤ (Finset.univ.biUnion (fun i => (s i).product (t i))).card := Finset.card_le_card hsub
      _ ≤ ∑ i, ((s i).product (t i)).card := Finset.card_biUnion_le
      _ = ∑ i, (s i).card * (t i).card := Finset.sum_congr rfl fun i _ => Finset.card_product (s i) (t i)
  have hu : (∑ i, (s i).card * (t i).card) ≤ 4 * m := by
    calc
      _ ≤ ∑ i : Fin m, 4 := Finset.sum_le_sum fun i _ =>
        (rectangle_count (s i) (t i) (hs i) (ht i) (hrect i)).1
      _ = 4 * m := by simp [Nat.mul_comm]
  have hm : 13 ≤ m := by omega
  have hid : (∑ i, ((s i).card + (t i).card)) =
      (∑ i, (s i).card * (t i).card) + m := by
    calc
      _ = ∑ i, ((s i).card * (t i).card + 1) :=
        Finset.sum_congr rfl fun i _ =>
          (rectangle_count (s i) (t i) (hs i) (ht i) (hrect i)).2
      _ = _ := by simp [Finset.sum_add_distrib]
  constructor
  · exact hm
  · omega

lemma private_neighbor (a : Fin 13) (s : Finset (Fin 13))
    (ha : a ∉ s) (hs : s.card ≤ 3) :
    ∃ l : Fin 13, incident a l ∧ ∀ p ∈ s, ¬ incident p l := by
  classical
  by_contra hn
  have covered : ∀ l ∈ neighbors a, ∃ p ∈ s, incident p l := by
    intro l hl
    by_contra hp
    apply hn
    exact ⟨l, (Finset.mem_filter.mp hl).2, fun p hps hpl => hp ⟨p, hps, hpl⟩⟩
  have hsub : neighbors a ⊆ s.biUnion (fun p => neighbors a ∩ neighbors p) := by
    intro l hl
    obtain ⟨p, hp, hpl⟩ := covered l hl
    exact Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_inter.mpr ⟨hl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩⟩
  have small : ∀ p ∈ s, (neighbors a ∩ neighbors p).card ≤ 1 := by
    intro p hp
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have hac := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2
    have hpc := (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2
    have had := (Finset.mem_filter.mp (Finset.mem_inter.mp hd).1).2
    have hpd := (Finset.mem_filter.mp (Finset.mem_inter.mp hd).2).2
    by_contra hcd
    have hap : a ≠ p := fun he => ha (he ▸ hp)
    exact no_rectangle a p c d hap hcd hac had hpc hpd
  have hfour : 4 ≤ s.card := by
    calc
      4 = (neighbors a).card := (neighbors_card a).symm
      _ ≤ (s.biUnion (fun p => neighbors a ∩ neighbors p)).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ s, (neighbors a ∩ neighbors p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ s, 1 := Finset.sum_le_sum small
      _ = s.card := by simp
  omega

lemma four_points_few_avoiding : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    (Finset.univ.filter fun l : Fin 13 =>
      ¬ incident a l ∧ ¬ incident b l ∧ ¬ incident c l ∧ ¬ incident d l).card ≤ 3 := by
  decide +kernel

lemma independent_small_side (s t : Finset (Fin 13))
    (h : ∀ p ∈ s, ∀ l ∈ t, ¬ incident p l) : s.card ≤ 3 ∨ t.card ≤ 3 := by
  by_cases hs : s.card ≤ 3
  · exact Or.inl hs
  right
  obtain ⟨s', hsub, hc⟩ := Finset.exists_subset_card_eq (s := s) (n := 4) (by omega)
  let f := s'.orderEmbOfFin hc
  have hm : ∀ i, f i ∈ s := fun i => hsub (s'.orderEmbOfFin_mem hc i)
  have hk := four_points_few_avoiding (f 0) (f 1) (f 2) (f 3)
    (f.strictMono (by decide)) (f.strictMono (by decide)) (f.strictMono (by decide))
  have hts : t ⊆ Finset.univ.filter fun l : Fin 13 =>
      ¬ incident (f 0) l ∧ ¬ incident (f 1) l ∧ ¬ incident (f 2) l ∧ ¬ incident (f 3) l := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h _ (hm 0) l hl, h _ (hm 1) l hl, h _ (hm 2) l hl, h _ (hm 3) l hl⟩
  exact (Finset.card_le_card hts).trans hk

lemma no_simultaneous_neighborhood_domination
    (s t : Finset (Fin 13)) (a b : Fin 13)
    (h : ∀ p ∈ s, ∀ l ∈ t, ¬ incident p l) (ha : a ∉ s) (hb : b ∉ t)
    (hpa : ∀ l, incident a l → ∃ p ∈ s, incident p l)
    (hlb : ∀ p, incident p b → ∃ l ∈ t, incident p l) : False := by
  rcases independent_small_side s t h with hs | ht
  · obtain ⟨l, hal, hsl⟩ := private_neighbor a s ha hs
    obtain ⟨p, hp, hpl⟩ := hpa l hal
    exact hsl p hp hpl
  · obtain ⟨p, hbp, htp⟩ := private_neighbor b t hb ht
    obtain ⟨l, hl, hpl⟩ := hlb p ((incident_symmetric b p).mp hbp)
    exact htp l hl ((incident_symmetric p l).mp hpl)

end PEqualNP.Outside.L_meta_2056_aux
