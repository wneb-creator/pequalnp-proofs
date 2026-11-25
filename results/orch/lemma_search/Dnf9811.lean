import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811_aux

def dnf {α : Type} (cs : List (List α)) (x : α → Bool) : Bool :=
  cs.any (fun c => c.all x)

lemma dnf_eq_of_subsumption {α : Type} (S T : List (List α))
    (hST : ∀ c ∈ S, ∃ d ∈ T, ∀ a ∈ d, a ∈ c)
    (hTS : ∀ c ∈ T, ∃ d ∈ S, ∀ a ∈ d, a ∈ c)
    (x : α → Bool) : dnf S x = dnf T x := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnf, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨c, hc, hx⟩
    obtain ⟨d, hd, hsub⟩ := hST c hc
    exact ⟨d, hd, fun a ha => hx a (hsub a ha)⟩
  · rintro ⟨c, hc, hx⟩
    obtain ⟨d, hd, hsub⟩ := hTS c hc
    exact ⟨d, hd, fun a ha => hx a (hsub a ha)⟩

lemma dnf_relabel {α β : Type} (cs : List (List α)) (ren : α → β)
    (x : β → Bool) : dnf cs (x ∘ ren) = dnf (cs.map (List.map ren)) x := by
  simp [dnf, List.any_map, List.all_map, Function.comp_def]

def pinClauses {α β : Type} [DecidableEq α] (cs : List (List α))
    (p : α) (b : Bool) (ren : α → β) : List (List β) :=
  (cs.filter (fun c => b || decide (p ∉ c))).map
    (fun c => (c.filter (fun a => decide (a ≠ p))).map ren)

lemma dnf_pin_relabel {α β : Type} [DecidableEq α] (cs : List (List α))
    (p : α) (b : Bool) (ren : α → β) (x : β → Bool) :
    dnf cs (Function.update (x ∘ ren) p b) = dnf (pinClauses cs p b ren) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnf, pinClauses, List.any_eq_true, List.all_eq_true,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨c, hc, hx⟩
    refine ⟨(c.filter (fun a => decide (a ≠ p))).map ren, ?_, ?_⟩
    · refine ⟨c, ⟨hc, ?_⟩, rfl⟩
      by_cases hp : p ∈ c
      · have hb := hx p hp
        simp only [Function.update_self] at hb
        simp [hb]
      · simp [hp]
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      obtain ⟨hqc, hqp⟩ := List.mem_filter.mp hq
      have hne : q ≠ p := of_decide_eq_true hqp
      simpa [Function.update_of_ne hne, Function.comp_def] using hx q hqc
  · rintro ⟨d, ⟨c, ⟨hc, hcb⟩, rfl⟩, hx⟩
    refine ⟨c, hc, ?_⟩
    intro a ha
    by_cases hap : a = p
    · subst a
      have hb : b = true := by simpa [ha] using hcb
      simpa using hb
    · have hv := hx (ren a) (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨ha, by simpa using hap⟩, rfl⟩)
      simpa [Function.update_of_ne hap, Function.comp_def] using hv

end PEqualNP.Outside.L_meta_9811_aux
