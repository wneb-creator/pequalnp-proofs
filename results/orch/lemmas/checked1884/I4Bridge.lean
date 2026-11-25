import PetersenGeometry
import MatchingPrivate

namespace PEqualNP.Outside.L_meta_1884_aux.I4Bridge

open PEqualNP.Outside.L_meta_2590_aux.Surplus

def profile (D : Dag) (b : Fin 10 → Nat) (x : Fin 10) : Finset (Sigma (fun _ : Nat => Nat)) :=
  (residualUnits 10 D b).filter fun u => x ∈ supp 10 D u.1

def centers (D : Dag) (b : Fin 10 → Nat) (c : Fin 10) : Finset (Fin 10) :=
  (ineligSet 10 D).filter fun i =>
    ∃ x ∈ eligSet 10 D, profile D b x ⊆ profile D b c ∧ Adj i x

set_option synthInstance.maxSize 12000 in
theorem avoiding_label : ∀ i x c : Fin 10,
    Adj i x → c ≠ i → c ≠ x →
    ∃ a, Adj i a ∧ a ≠ x ∧ a ≠ c ∧ ¬ Adj a c := by
  unfold Adj
  decide +kernel

theorem dominated_assigned {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    {i x c : Fin 10} (hi : i ∈ ineligSet 10 D) (hix : Adj i x)
    (hc : c ∈ eligSet 10 D) (hcx : c ≠ x)
    (hd : ∃ e0, ∀ e ∈ sem_W 10 D x, e ≠ e0 → c ∈ supp 10 D (src D e)) :
    pos i ∈ sem_W 10 D c := by
  obtain ⟨e0, hd⟩ := hd
  obtain ⟨hp, hp0, hpn, _⟩ := hpos.1 i hi
  have hpx : pos i ∈ sem_W 10 D x := sem_mem_W.mpr
    ⟨hp, hpn x hix, by rw [hp0]; exact Finset.notMem_empty _⟩
  have hci : c ≠ i := fun hh => (sem_mem_inelig.mp hi) (hh ▸ hc)
  obtain ⟨a, hia, hax, hac, hnac⟩ := avoiding_label i x c hix hci hcx
  refine sem_mem_W.mpr ⟨hp, ?_, by rw [hp0]; exact Finset.notMem_empty _⟩
  by_contra hcn
  have hie : pos i = e0 := by
    by_contra hn
    exact hcn (hd _ hpx hn)
  obtain ⟨f, hf, hfa, hfc⟩ := sem_pg_cover_free h hD (Ne.symm hax) (Ne.symm hcx) hnac
  have hfe : f = e0 := by
    by_contra hn
    exact hfc (hd _ hf hn)
  rw [hfe, ← hie] at hfa
  exact hfa (hpn a hia)

theorem profile_assigned {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    {x c : Fin 10} (hx : x ∈ eligSet 10 D) (hc : c ∈ eligSet 10 D)
    (hne : (profile D b x).Nonempty) (hsub : profile D b x ⊆ profile D b c)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) (hix : Adj i x) :
    pos i ∈ sem_W 10 D c := by
  by_cases hxc : x = c
  · subst x
    obtain ⟨hp, hp0, hpn, _⟩ := hpos.1 i hi
    exact sem_mem_W.mpr ⟨hp, hpn c hix, by rw [hp0]; exact Finset.notMem_empty _⟩
  obtain ⟨u, hu⟩ := hne
  obtain ⟨hur, hux⟩ := Finset.mem_filter.mp hu
  have huc := (Finset.mem_filter.mp (hsub hu)).2
  have hd := ri_gen sem_petersen_gr h hD b hb hxc hx
    (fun v hv hxv => (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hv, hxv⟩))).2)
    (w := u.1) ⟨hux, huc⟩
  exact dominated_assigned h hD hpos hi hix hc (Ne.symm hxc) hd

theorem center_image {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    (hne : ∀ x ∈ eligSet 10 D, (profile D b x).Nonempty)
    {c : Fin 10} (hc : c ∈ eligSet 10 D) :
    (centers D b c).image pos ⊆ sem_W 10 D c ∧
    ((centers D b c).image pos).card = (centers D b c).card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi, x, hx, hsub, hix⟩ := Finset.mem_filter.mp hi
    exact profile_assigned h hD b hb hpos hx hc (hne x hx) hsub hi hix
  · exact Finset.card_image_of_injOn
      (fun i hi j hj hij => hpos.2 i (Finset.mem_filter.mp hi).1
        j (Finset.mem_filter.mp hj).1 hij)

theorem center_budget {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → Nat) (hb : PureBranch 10 D b)
    {pos : Fin 10 → Nat × Bool} (hpos : k4_Pos 10 Adj D pos)
    (hne : ∀ x ∈ eligSet 10 D, (profile D b x).Nonempty)
    {c y : Fin 10} (hc : c ∈ eligSet 10 D) (hy : y ∈ eligSet 10 D) (hcy : Adj c y) :
    (centers D b c).card ≤ (profile D b c).card + 1 := by
  obtain ⟨e, he, _, hep, _, _, _⟩ :=
    MatchingPrivate.eligible_edge_private_pair sem_petersen_gr h hD hpos hc hy hcy
  obtain ⟨hsub, hcard⟩ := center_image h hD b hb hpos hne hc
  have hnot : e ∉ (centers D b c).image pos := by
    intro hec
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hec
    exact hep (Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, hie⟩)
  have hcount := Finset.card_le_card (Finset.insert_subset he hsub)
  rw [Finset.card_insert_of_notMem hnot, hcard] at hcount
  have hflow := sem_code_count sem_petersen_gr h hD b hb c
  have hint : ({c} ∩ eligSet 10 D).card = 1 := by simp [hc]
  rw [hint] at hflow
  change _ + _ = _ + (profile D b c).card at hflow
  omega

end PEqualNP.Outside.L_meta_1884_aux.I4Bridge
