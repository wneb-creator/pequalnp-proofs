import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankGeometry

lemma pencil_card : ∀ p : Fin 13,
    (Finset.univ.filter (fun w : Fin 13 => p ∈ Global.line w)).card = 4 := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma avoid_three_card : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    (Finset.univ.filter (fun w : Fin 13 =>
      a ∉ Global.line w ∧ b ∉ Global.line w ∧ c ∉ Global.line w)).card ≤ 4 := by
  decide +kernel

lemma five_lines_not_all_through (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (p : Fin 13) : ∃ e : Fin 5, p ∉ Global.line (lineId e) := by
  classical
  by_contra! hall
  have hsub : Finset.univ.image lineId ⊆
      Finset.univ.filter (fun w : Fin 13 => p ∈ Global.line w) := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall e⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, pencil_card] at hc
  have he : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  omega

lemma five_line_union_card (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) :
    11 ≤ (Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))).card := by
  classical
  let U := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  change 11 ≤ U.card
  by_contra! hsmall
  have hcomp : 3 ≤ (Finset.univ \ U).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  obtain ⟨a, b, c, hab, hac, hbc, hT⟩ := Finset.card_eq_three.mp hTcard
  have hnot (p : Fin 13) (hp : p ∈ T) (e : Fin 5) : p ∉ Global.line (lineId e) := by
    intro he
    exact (Finset.mem_sdiff.mp (hTsub hp)).2
      (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, he⟩)
  have hsub : Finset.univ.image lineId ⊆ Finset.univ.filter (fun w : Fin 13 =>
      a ∉ Global.line w ∧ b ∉ Global.line w ∧ c ∉ Global.line w) := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hnot a (by simp [hT]) e, hnot b (by simp [hT]) e, hnot c (by simp [hT]) e⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hc
  have hf := avoid_three_card a b c hab hac hbc
  have he : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  omega

end PEqualNP.Outside.L_meta_1024_aux.ParentRankGeometry

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

def Shared (parent : Fin 5 → Bool → ℕ) (e f : Fin 5) : Prop :=
  ∃ a b : Bool, parent e a = parent f b

def Connected (parent : Fin 5 → Bool → ℕ) : Prop :=
  ∀ e f : Fin 5, Relation.ReflTransGen (Shared parent) e f

def DegreeTwo (parent : Fin 5 → Bool → ℕ) : Prop :=
  ∀ e : Fin 5, ∀ a : Bool, ∃ f : Fin 5, e ≠ f ∧ ∃ b : Bool, parent e a = parent f b

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_avoids_two : ∀ a b c : Fin 13, a ≠ b → a ≠ c →
    ∃ p ∈ Global.line a, p ∉ Global.line b ∧ p ∉ Global.line c := by
  decide +kernel

lemma connected_degree_two_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent) (hdegree : DegreeTwo parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  have hend (e : Fin 5) : wire (parent e false) = wire (parent e true) := by
    obtain ⟨f, hef, b, hfb⟩ := hdegree e false
    obtain ⟨g, heg, c, hgc⟩ := hdegree e true
    obtain ⟨p, hp, hpf, hpg⟩ := line_avoids_two (lineId e) (lineId f) (lineId g)
      (fun h => hef (hinj h)) (fun h => heg (hinj h))
    have h₁ := hforce e f hef false b hfb p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)
    have h₂ := hforce e g heg true c hgc p (Finset.mem_sdiff.mpr ⟨hp, hpg⟩)
    exact h₂.symm.trans h₁
  have hend' (e : Fin 5) (a : Bool) : wire (parent e a) = wire (parent e false) := by
    cases a
    · rfl
    · exact (hend e).symm
  have hadj (e f : Fin 5) (h : Shared parent e f) :
      wire (parent e false) = wire (parent f false) := by
    obtain ⟨a, b, hab⟩ := h
    exact (hend' e a).symm.trans ((congrArg wire hab).trans (hend' f b))
  have hpath (e f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) :
      wire (parent e false) = wire (parent f false) := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih => exact ih.trans (hadj _ _ hlast)
  let c := wire (parent 0 false)
  have hconst (e : Fin 5) (a : Bool) : wire (parent e a) = c :=
    (hend' e a).trans (hpath e 0 (hconn e 0))
  have hpoint (p : Fin 13) (e : Fin 5) (hp : p ∈ Global.line (lineId e)) : label p = c := by
    by_contra hn
    have hstep (e f : Fin 5) (h : Shared parent e f)
        (hp : p ∈ Global.line (lineId e)) : p ∈ Global.line (lineId f) := by
      by_cases hef : e = f
      · simpa [hef] using hp
      obtain ⟨a, b, hab⟩ := h
      by_contra hpf
      exact hn ((hforce e f hef a b hab p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)).trans (hconst e (!a)))
    have hall (f : Fin 5) : p ∈ Global.line (lineId f) := by
      have h := hconn e f
      induction h with
      | refl => exact hp
      | tail hprev hlast ih => exact hstep _ _ hlast ih
    obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
    exact hpf (hall f)
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  have hS : 11 ≤ S.card := ParentRankGeometry.five_line_union_card lineId hinj
  have himage : S.image label ⊆ {c} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_singleton.mpr (hpoint p e hpe)
  have hcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himage
  exact ⟨S, by omega⟩

lemma linewise_rank
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (label : Fin 13 → ℕ) (value : Fin 5 → ℕ)
    (hline : ∀ e : Fin 5, ∀ p ∈ Global.line (lineId e), label p = value e) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  have hvalue (e : Fin 5) : value e = value 0 := by
    by_cases he : e = 0
    · rw [he]
    obtain ⟨p, hpe, hp0⟩ := (Bridge.pair_geometry (lineId e) (lineId 0)
      (fun h => he (hinj h))).2
    exact (hline e p hpe).symm.trans (hline 0 p hp0)
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  have hS : 11 ≤ S.card := ParentRankGeometry.five_line_union_card lineId hinj
  have himage : S.image label ⊆ {value 0} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e, _, hpe⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_singleton.mpr ((hline e p hpe).trans (hvalue e))
  have hcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himage
  exact ⟨S, by omega⟩

lemma star_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (center : ℕ) (side : Fin 5 → Bool) (hstar : ∀ e, parent e (side e) = center) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  apply linewise_rank lineId hinj label (fun e => wire (parent e (!(side e))))
  intro e p hp
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  have hef : e ≠ f := by
    intro he
    subst f
    exact hpf hp
  exact hforce e f hef (side e) (side f) ((hstar e).trans (hstar f).symm) p
    (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)


def Nonleaf (parent : Fin 5 → Bool → ℕ) (v : ℕ) : Prop :=
  ∃ e f : Fin 5, e ≠ f ∧ ∃ a b : Bool, parent e a = v ∧ parent f b = v

def CoreEdge (parent : Fin 5 → Bool → ℕ) (e : Fin 5) : Prop :=
  Nonleaf parent (parent e false) ∧ Nonleaf parent (parent e true)

lemma nonleaf_other (parent : Fin 5 → Bool → ℕ) (e : Fin 5) (a : Bool)
    (h : Nonleaf parent (parent e a)) :
    ∃ f : Fin 5, e ≠ f ∧ ∃ b : Bool, parent e a = parent f b := by
  obtain ⟨f, g, hfg, b, c, hfb, hgc⟩ := h
  by_cases hef : e = f
  · subst f
    exact ⟨g, hfg, c, hgc.symm⟩
  · exact ⟨f, hef, b, hfb.symm⟩

lemma shared_nonleaf (parent : Fin 5 → Bool → ℕ) (e f : Fin 5)
    (hef : e ≠ f) (a b : Bool) (h : parent e a = parent f b) :
    Nonleaf parent (parent e a) :=
  ⟨e, f, hef, a, b, rfl, h.symm⟩

lemma edge_has_nonleaf (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (e : Fin 5) : ∃ a : Bool, Nonleaf parent (parent e a) := by
  classical
  by_contra hn
  have hnone (a : Bool) : ¬ Nonleaf parent (parent e a) := by
    intro ha
    exact hn ⟨a, ha⟩
  have hadj (f : Fin 5) (h : Shared parent e f) : e = f := by
    by_contra hef
    obtain ⟨a, b, hab⟩ := h
    exact hnone a (shared_nonleaf parent e f hef a b hab)
  have hpath (f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) : e = f := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih =>
      apply hadj
      simpa only [ih] using hlast
  have h01 := (hpath 0 (hconn e 0)).symm.trans (hpath 1 (hconn e 1))
  exact (by decide : (0 : Fin 5) ≠ 1) h01

lemma core_end_equal
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (e : Fin 5) (he : CoreEdge parent e) :
    wire (parent e false) = wire (parent e true) := by
  obtain ⟨f, hef, b, hfb⟩ := nonleaf_other parent e false he.1
  obtain ⟨g, heg, c, hgc⟩ := nonleaf_other parent e true he.2
  obtain ⟨p, hp, hpf, hpg⟩ := line_avoids_two (lineId e) (lineId f) (lineId g)
    (fun h => hef (hinj h)) (fun h => heg (hinj h))
  have h₁ := hforce e f hef false b hfb p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)
  have h₂ := hforce e g heg true c hgc p (Finset.mem_sdiff.mpr ⟨hp, hpg⟩)
  exact h₂.symm.trans h₁

lemma nonleaf_values_equal
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ c : ℕ, ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c := by
  classical
  choose anchor hanchor using edge_has_nonleaf parent hconn
  have hedge (e : Fin 5) (a : Bool) (ha : Nonleaf parent (parent e a)) :
      wire (parent e a) = wire (parent e (anchor e)) := by
    by_cases hea : a = anchor e
    · rw [hea]
    have hae := hanchor e
    have he : CoreEdge parent e := by
      cases a <;> cases h : anchor e <;> simp_all [CoreEdge]
    have heq := core_end_equal parent lineId hinj label wire hforce e he
    cases a <;> cases h : anchor e <;> simp_all
  have hadj (e f : Fin 5) (h : Shared parent e f) :
      wire (parent e (anchor e)) = wire (parent f (anchor f)) := by
    by_cases hef : e = f
    · rw [hef]
    obtain ⟨a, b, hab⟩ := h
    have hna := shared_nonleaf parent e f hef a b hab
    have hnb : Nonleaf parent (parent f b) := hab ▸ hna
    exact (hedge e a hna).symm.trans ((congrArg wire hab).trans (hedge f b hnb))
  have hpath (e f : Fin 5) (h : Relation.ReflTransGen (Shared parent) e f) :
      wire (parent e (anchor e)) = wire (parent f (anchor f)) := by
    induction h with
    | refl => rfl
    | tail hprev hlast ih => exact ih.trans (hadj _ _ hlast)
  exact ⟨wire (parent 0 (anchor 0)), fun e a ha =>
    (hedge e a ha).trans (hpath e 0 (hconn e 0))⟩

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

lemma core_points
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hcommon : ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c)
    (e : Fin 5) (he : CoreEdge parent e) :
    ∀ p ∈ Global.line (lineId e), label p = c := by
  intro p hp
  by_contra hn
  let AllAt (v : ℕ) : Prop := ∀ f : Fin 5, ∀ b : Bool,
    parent f b = v → p ∈ Global.line (lineId f)
  have transfer (f : Fin 5) (a : Bool) (hf : p ∈ Global.line (lineId f))
      (hopp : Nonleaf parent (parent f (!a))) : AllAt (parent f a) := by
    intro g b hgb
    by_cases hfg : f = g
    · simpa [hfg] using hf
    by_contra hpg
    exact hn ((hforce f g hfg a b hgb.symm p
      (Finset.mem_sdiff.mpr ⟨hf, hpg⟩)).trans (hcommon f (!a) hopp))
  have hstart : ∀ a : Bool, Nonleaf parent (parent e a) → AllAt (parent e a) := by
    intro a ha
    apply transfer e a hp
    cases a
    · exact he.2
    · exact he.1
  have hstep (f g : Fin 5) (hfg : Shared parent f g)
      (hf : ∀ a : Bool, Nonleaf parent (parent f a) → AllAt (parent f a)) :
      ∀ b : Bool, Nonleaf parent (parent g b) → AllAt (parent g b) := by
    by_cases heq : f = g
    · simpa [heq] using hf
    obtain ⟨a, b, hab⟩ := hfg
    have hna := shared_nonleaf parent f g heq a b hab
    have hnb : Nonleaf parent (parent g b) := hab ▸ hna
    have hat : AllAt (parent g b) := hab ▸ hf a hna
    have hpg := hat g b rfl
    intro d hd
    by_cases hdb : d = b
    · simpa [hdb] using hat
    apply transfer g d hpg
    have hnot : (!d) = b := by cases d <;> cases b <;> simp_all
    simpa only [hnot] using hnb
  have hreach (f : Fin 5) : ∀ a : Bool,
      Nonleaf parent (parent f a) → AllAt (parent f a) := by
    have h := hconn e f
    induction h with
    | refl => exact hstart
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  obtain ⟨a, ha⟩ := edge_has_nonleaf parent hconn f
  exact hpf (hreach f a ha f a rfl)


def Incident (parent : Fin 5 → Bool → ℕ) (v : ℕ) (e : Fin 5) : Prop :=
  ∃ a : Bool, parent e a = v

lemma star_of_no_core_neighbor (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (v : ℕ) (hv : Nonleaf parent v)
    (hno : ∀ e : Fin 5, Incident parent v e → ¬ CoreEdge parent e) :
    ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v := by
  classical
  have hstep (e f : Fin 5) (h : Shared parent e f) (he : Incident parent v e) :
      Incident parent v f := by
    by_cases hef : e = f
    · simpa [hef] using he
    obtain ⟨a, b, hab⟩ := h
    obtain ⟨d, hd⟩ := he
    by_cases hda : d = a
    · exact ⟨b, hab.symm.trans (hda ▸ hd)⟩
    have hna := shared_nonleaf parent e f hef a b hab
    have hnd : Nonleaf parent (parent e d) := hd.symm ▸ hv
    have hc : CoreEdge parent e := by
      cases d <;> cases a <;> simp_all [CoreEdge]
    exact False.elim (hno e ⟨d, hd⟩ hc)
  obtain ⟨e, f, hef, a, b, hea, hfb⟩ := hv
  have hall (g : Fin 5) : Incident parent v g := by
    have h := hconn e g
    induction h with
    | refl => exact ⟨a, hea⟩
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  exact ⟨fun e => Classical.choose (hall e), fun e => Classical.choose_spec (hall e)⟩

lemma core_neighbor_of_not_star (parent : Fin 5 → Bool → ℕ) (hconn : Connected parent)
    (hstar : ¬ ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v)
    (v : ℕ) (hv : Nonleaf parent v) :
    ∃ e : Fin 5, Incident parent v e ∧ CoreEdge parent e := by
  by_contra! hno
  obtain ⟨side, hs⟩ := star_of_no_core_neighbor parent hconn v hv hno
  exact hstar ⟨v, side, hs⟩


lemma line_inter_unique (a b : Fin 13) (hab : a ≠ b) (p q : Fin 13)
    (hpa : p ∈ Global.line a) (hpb : p ∈ Global.line b)
    (hqa : q ∈ Global.line a) (hqb : q ∈ Global.line b) : p = q := by
  exact Finset.card_le_one.mp (Global.line_intersection a b hab) p
    (Finset.mem_inter.mpr ⟨hpa, hpb⟩) q (Finset.mem_inter.mpr ⟨hqa, hqb⟩)

lemma bad_endpoint_pencil
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (hstar : ¬ ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hcommon : ∀ e : Fin 5, ∀ a : Bool, Nonleaf parent (parent e a) →
      wire (parent e a) = c)
    (e : Fin 5) (a : Bool) (hbad : wire (parent e a) ≠ c) :
    ∃ p ∈ Global.line (lineId e),
      (∀ f : Fin 5, CoreEdge parent f → p ∈ Global.line (lineId f)) ∧
      (∀ q ∈ Global.line (lineId e), q ≠ p → label q = wire (parent e a)) := by
  classical
  have hleaf : ¬ Nonleaf parent (parent e a) := fun h => hbad (hcommon e a h)
  have hne : ¬ CoreEdge parent e := by
    intro he
    apply hleaf
    cases a
    · exact he.1
    · exact he.2
  have hother : Nonleaf parent (parent e (!a)) := by
    obtain ⟨b, hb⟩ := edge_has_nonleaf parent hconn e
    cases a <;> cases b <;> simp_all
  obtain ⟨f, ⟨b, hfb⟩, hfc⟩ :=
    core_neighbor_of_not_star parent hconn hstar (parent e (!a)) hother
  have hef : e ≠ f := by intro h; exact hne (h.symm ▸ hfc)
  have hids : lineId e ≠ lineId f := fun h => hef (hinj h)
  obtain ⟨p, hpe, hpf⟩ := (Bridge.pair_geometry (lineId e) (lineId f) hids).2
  have hpartial (q : Fin 13) (hqe : q ∈ Global.line (lineId e)) (hqp : q ≠ p) :
      label q = wire (parent e a) := by
    have hqf : q ∉ Global.line (lineId f) := by
      intro hqf
      exact hqp (line_inter_unique (lineId e) (lineId f) hids q p hqe hqf hpe hpf)
    have h := hforce e f hef (!a) b hfb.symm q (Finset.mem_sdiff.mpr ⟨hqe, hqf⟩)
    simpa using h
  refine ⟨p, hpe, ?_, hpartial⟩
  intro g hgc
  have heg : e ≠ g := by intro h; exact hne (h.symm ▸ hgc)
  obtain ⟨q, hqe, hqg⟩ := (Bridge.pair_geometry (lineId e) (lineId g)
    (fun h => heg (hinj h))).2
  by_cases hqp : q = p
  · simpa only [hqp] using hqg
  have hqc := core_points parent lineId hinj hconn label wire hforce c hcommon g hgc q hqg
  exact False.elim (hbad ((hpartial q hqe hqp).symm.trans hqc))

lemma all_values_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (c : ℕ) (hvalues : ∀ e : Fin 5, ∀ a : Bool, wire (parent e a) = c) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  apply linewise_rank lineId hinj label (fun _ => c)
  intro e p hp
  by_contra hn
  have hstep (e f : Fin 5) (h : Shared parent e f)
      (hp : p ∈ Global.line (lineId e)) : p ∈ Global.line (lineId f) := by
    by_cases hef : e = f
    · simpa [hef] using hp
    obtain ⟨a, b, hab⟩ := h
    by_contra hpf
    exact hn ((hforce e f hef a b hab p (Finset.mem_sdiff.mpr ⟨hp, hpf⟩)).trans (hvalues e (!a)))
  have hall (f : Fin 5) : p ∈ Global.line (lineId f) := by
    have h := hconn e f
    induction h with
    | refl => exact hp
    | tail hprev hlast ih => exact hstep _ _ hlast ih
  obtain ⟨f, hpf⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  exact hpf (hall f)

lemma two_core_edges_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (f g : Fin 5) (hfg : f ≠ g) (hfc : CoreEdge parent f) (hgc : CoreEdge parent g) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨c, hcommon⟩ := nonleaf_values_equal parent lineId hinj hconn label wire hforce
  apply all_values_rank parent lineId hinj hconn label wire hforce c
  intro e a
  by_contra hbad
  obtain ⟨p, hpe, hpall, hpartial⟩ :=
    bad_endpoint_pencil parent lineId hinj hconn hstar label wire hforce c hcommon e a hbad
  obtain ⟨n, hpn⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj p
  have hnwire (b : Bool) : wire (parent n b) = c := by
    by_contra hbadn
    obtain ⟨q, hqn, hqall, _⟩ :=
      bad_endpoint_pencil parent lineId hinj hconn hstar label wire hforce c hcommon n b hbadn
    have hqp := line_inter_unique (lineId f) (lineId g) (fun h => hfg (hinj h))
      q p (hqall f hfc) (hqall g hgc) (hpall f hfc) (hpall g hgc)
    exact hpn (hqp ▸ hqn)
  obtain ⟨b, hb⟩ := edge_has_nonleaf parent hconn n
  obtain ⟨k, ⟨d, hkd⟩, hkc⟩ :=
    core_neighbor_of_not_star parent hconn hstar (parent n b) hb
  have hnk : n ≠ k := by
    intro h
    exact hpn (h.symm ▸ hpall k hkc)
  have hen : e ≠ n := by intro h; exact hpn (h ▸ hpe)
  obtain ⟨q, hqe, hqn⟩ := (Bridge.pair_geometry (lineId e) (lineId n)
    (fun h => hen (hinj h))).2
  have hqp : q ≠ p := by intro h; exact hpn (h ▸ hqn)
  have hek : e ≠ k := by
    intro h
    have hec : CoreEdge parent e := h.symm ▸ hkc
    have hea : Nonleaf parent (parent e a) := by cases a; exact hec.1; exact hec.2
    exact hbad (hcommon e a hea)
  have hqk : q ∉ Global.line (lineId k) := by
    intro hqk
    exact hqp (line_inter_unique (lineId e) (lineId k) (fun h => hek (hinj h))
      q p hqe hqk hpe (hpall k hkc))
  have hqwire := hforce n k hnk b d hkd.symm q (Finset.mem_sdiff.mpr ⟨hqn, hqk⟩)
  exact hbad ((hpartial q hqe hqp).symm.trans (hqwire.trans (hnwire (!b))))

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

namespace PEqualNP.Outside.L_meta_1024_aux.ParentRankCore

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma pencil_avoid_two : ∀ a q r : Fin 13, q ≠ r →
    let A := Finset.univ.filter (fun w : Fin 13 =>
      a ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
    A.card ≤ 3 ∧ (A.card ≤ 2 ∨ ∃ w : Fin 13,
      a ∈ Global.line w ∧ q ∈ Global.line w ∧ r ∈ Global.line w) := by
  decide +kernel

lemma line_eq_of_two (a b p q : Fin 13) (hpq : p ≠ q)
    (hpa : p ∈ Global.line a) (hpb : p ∈ Global.line b)
    (hqa : q ∈ Global.line a) (hqb : q ∈ Global.line b) : a = b := by
  by_contra hab
  exact hpq (line_inter_unique a b hab p q hpa hpb hqa hqb)

lemma pencil_pair_union_card
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (d : Fin 5) (a b : Fin 13) (hab : a ≠ b)
    (had : a ∈ Global.line (lineId d)) (hbd : b ∈ Global.line (lineId d))
    (hfamily : ∀ e : Fin 5, a ∈ Global.line (lineId e) ∨ b ∈ Global.line (lineId e)) :
    12 ≤ (Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))).card := by
  classical
  let S := Finset.univ.biUnion (fun e : Fin 5 => Global.line (lineId e))
  change 12 ≤ S.card
  by_contra! hsmall
  have hcomp : 2 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcomp
  obtain ⟨q, r, hqr, hT⟩ := Finset.card_eq_two.mp hTcard
  have hmissing (p : Fin 13) (hp : p ∈ T) (e : Fin 5) : p ∉ Global.line (lineId e) := by
    intro he
    exact (Finset.mem_sdiff.mp (hTsub hp)).2
      (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, he⟩)
  have hq (e : Fin 5) := hmissing q (by simp [hT]) e
  have hr (e : Fin 5) := hmissing r (by simp [hT]) e
  let A := Finset.univ.filter (fun w : Fin 13 =>
    a ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
  let B := Finset.univ.filter (fun w : Fin 13 =>
    b ∈ Global.line w ∧ q ∉ Global.line w ∧ r ∉ Global.line w)
  obtain ⟨hA3, hAcases⟩ := pencil_avoid_two a q r hqr
  obtain ⟨hB3, hBcases⟩ := pencil_avoid_two b q r hqr
  change A.card ≤ 3 at hA3
  change B.card ≤ 3 at hB3
  change A.card ≤ 2 ∨ _ at hAcases
  change B.card ≤ 2 ∨ _ at hBcases
  have hsum : A.card + B.card ≤ 5 := by
    rcases hAcases with hA2 | ⟨u, hau, hqu, hru⟩
    · omega
    rcases hBcases with hB2 | ⟨v, hbv, hqv, hrv⟩
    · omega
    have huv := line_eq_of_two u v q r hqr hqu hqv hru hrv
    have hbu : b ∈ Global.line u := huv.symm ▸ hbv
    have hdu := line_eq_of_two (lineId d) u a b hab had hau hbd hbu
    exact False.elim (hq d (hdu.symm ▸ hqu))
  have hboth : lineId d ∈ A ∩ B := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hq d, hr d⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbd, hq d, hr d⟩⟩
  have hinter : 1 ≤ (A ∩ B).card := Finset.one_le_card.mpr ⟨_, hboth⟩
  have hsub : Finset.univ.image lineId ⊆ A ∪ B := by
    intro w hw
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hw
    rcases hfamily e with hae | hbe
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hae, hq e, hr e⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbe, hq e, hr e⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  have hfive : (Finset.univ : Finset (Fin 5)).card = 5 := by decide
  have hu := Finset.card_union_add_card_inter A B
  omega


lemma grouped_rank
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId)
    (d : Fin 5) (group : Fin 5 → Bool) (label : Fin 13 → ℕ)
    (value : Fin 5 → ℕ) (c : ℕ)
    (hcentral : ∀ p ∈ Global.line (lineId d), label p = c)
    (houtside : ∀ e : Fin 5, e ≠ d →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId d), label p = value e)
    (hsame : ∀ e f : Fin 5, e ≠ f → group e = group f →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f), label p = value e) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hvalues : ∀ e : Fin 5, e ≠ d → value e = c
  · apply linewise_rank lineId hinj label (fun _ => c)
    intro e p hp
    by_cases hpd : p ∈ Global.line (lineId d)
    · exact hcentral p hpd
    have hed : e ≠ d := by intro h; exact hpd (h ▸ hp)
    exact (houtside e hed p (Finset.mem_sdiff.mpr ⟨hp, hpd⟩)).trans (hvalues e hed)
  push Not at hvalues
  obtain ⟨e, hed, hbad⟩ := hvalues
  have family_pencil (f : Fin 5) (hfd : f ≠ d) (hbadf : value f ≠ c) :
      ∃ p ∈ Global.line (lineId f), p ∈ Global.line (lineId d) ∧
        (∀ k : Fin 5, group k = group f → p ∈ Global.line (lineId k)) := by
    obtain ⟨p, hpf, hpd⟩ := (Bridge.pair_geometry (lineId f) (lineId d)
      (fun h => hfd (hinj h))).2
    refine ⟨p, hpf, hpd, ?_⟩
    intro k hgroup
    by_cases hfk : f = k
    · simpa [hfk] using hpf
    by_contra hpk
    have hv := hsame f k hfk hgroup.symm p (Finset.mem_sdiff.mpr ⟨hpf, hpk⟩)
    exact hbadf (hv.symm.trans (hcentral p hpd))
  obtain ⟨a, hae, had, hA⟩ := family_pencil e hed hbad
  obtain ⟨n, han⟩ := ParentRankGeometry.five_lines_not_all_through lineId hinj a
  have hnd : n ≠ d := by intro h; exact han (h.symm ▸ had)
  have hne : n ≠ e := by intro h; exact han (h.symm ▸ hae)
  have hgroups : group n ≠ group e := by intro h; exact han (hA n h)
  obtain ⟨q, hqe, hqn⟩ := (Bridge.pair_geometry (lineId e) (lineId n)
    (fun h => hne (hinj h).symm)).2
  have hqd : q ∉ Global.line (lineId d) := by
    intro hqd
    have hqa := line_inter_unique (lineId e) (lineId d) (fun h => hed (hinj h))
      q a hqe hqd hae had
    exact han (hqa ▸ hqn)
  have hvn : value n = value e :=
    (houtside n hnd q (Finset.mem_sdiff.mpr ⟨hqn, hqd⟩)).symm.trans
      (houtside e hed q (Finset.mem_sdiff.mpr ⟨hqe, hqd⟩))
  have hbadn : value n ≠ c := fun h => hbad (hvn.symm.trans h)
  obtain ⟨b, hbn, hbd, hB⟩ := family_pencil n hnd hbadn
  have hab : a ≠ b := by intro h; exact han (h.symm ▸ hbn)
  have hgroupcases (f : Fin 5) : group f = group e ∨ group f = group n := by
    cases hf : group f <;> cases he : group e <;> cases hn : group n <;> simp_all
  have hfamily (f : Fin 5) : a ∈ Global.line (lineId f) ∨ b ∈ Global.line (lineId f) := by
    rcases hgroupcases f with hf | hf
    · exact Or.inl (hA f hf)
    · exact Or.inr (hB f hf)
  have hval (f : Fin 5) (hfd : f ≠ d) : value f = value e := by
    have common (k : Fin 5) (hkd : k ≠ d) (x y : Fin 13) (hxy : x ≠ y)
        (hxf : x ∈ Global.line (lineId f)) (hxd : x ∈ Global.line (lineId d))
        (hyk : y ∈ Global.line (lineId k)) (hyd : y ∈ Global.line (lineId d)) :
        value f = value k := by
      have hfk : f ≠ k := by
        intro h
        have hxy' := line_inter_unique (lineId f) (lineId d) (fun h => hfd (hinj h))
          x y hxf hxd (h.symm ▸ hyk) hyd
        exact hxy hxy'
      obtain ⟨z, hzf, hzk⟩ := (Bridge.pair_geometry (lineId f) (lineId k)
        (fun h => hfk (hinj h))).2
      have hzd : z ∉ Global.line (lineId d) := by
        intro hzd
        have hzx := line_inter_unique (lineId f) (lineId d) (fun h => hfd (hinj h))
          z x hzf hzd hxf hxd
        have hzy := line_inter_unique (lineId k) (lineId d) (fun h => hkd (hinj h))
          z y hzk hzd hyk hyd
        exact hxy (hzx.symm.trans hzy)
      exact (houtside f hfd z (Finset.mem_sdiff.mpr ⟨hzf, hzd⟩)).symm.trans
        (houtside k hkd z (Finset.mem_sdiff.mpr ⟨hzk, hzd⟩))
    rcases hgroupcases f with hf | hf
    · exact (common n hnd a b hab (hA f hf) had hbn hbd).trans hvn
    · exact common e hed b a hab.symm (hB f hf) hbd hae had
  let S := Finset.univ.biUnion (fun f : Fin 5 => Global.line (lineId f))
  have hS : 12 ≤ S.card := pencil_pair_union_card lineId hinj d a b hab had hbd hfamily
  have himage : S.image label ⊆ {c, value e} := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨f, _, hpf⟩ := Finset.mem_biUnion.mp hp
    by_cases hpd : p ∈ Global.line (lineId d)
    · exact Finset.mem_insert.mpr (Or.inl (hcentral p hpd))
    have hfd : f ≠ d := by intro h; exact hpd (h ▸ hpf)
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
      ((houtside f hfd p (Finset.mem_sdiff.mpr ⟨hpf, hpd⟩)).trans (hval f hfd))))
  have hcard : (S.image label).card ≤ 2 := by
    have h := Finset.card_le_card himage
    have hpair : ({c, value e} : Finset ℕ).card ≤ 2 := by
      by_cases hce : c = value e
      · simp [hce]
      · rw [Finset.card_pair hce]
    omega
  exact ⟨S, by omega⟩


lemma unique_core_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a)))
    (d : Fin 5) (hd : CoreEdge parent d)
    (hunique : ∀ e : Fin 5, CoreEdge parent e → e = d) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨c, hcommon⟩ := nonleaf_values_equal parent lineId hinj hconn label wire hforce
  choose anchor hanchor using edge_has_nonleaf parent hconn
  have hex (e : Fin 5) : ∃ b : Bool, parent e (anchor e) = parent d b := by
    obtain ⟨k, ⟨b, hkb⟩, hkc⟩ := core_neighbor_of_not_star parent hconn hstar
      (parent e (anchor e)) (hanchor e)
    exact ⟨b, hkb.symm.trans (congrArg (fun k => parent k b) (hunique k hkc))⟩
  choose arm harm using hex
  apply grouped_rank lineId hinj d arm label (fun e => wire (parent e (!(anchor e)))) c
  · exact core_points parent lineId hinj hconn label wire hforce c hcommon d hd
  · intro e hed p hp
    exact hforce e d hed (anchor e) (arm e) (harm e) p hp
  · intro e f hef hgroup p hp
    have hab : parent e (anchor e) = parent f (anchor f) :=
      (harm e).trans ((congrArg (fun b => parent d b) hgroup).trans (harm f).symm)
    exact hforce e f hef (anchor e) (anchor f) hab p hp

lemma connected_rank
    (parent : Fin 5 → Bool → ℕ) (lineId : Fin 5 → Fin 13)
    (hinj : Function.Injective lineId) (hconn : Connected parent)
    (label : Fin 13 → ℕ) (wire : ℕ → ℕ)
    (hforce : ∀ e f : Fin 5, e ≠ f → ∀ a b : Bool, parent e a = parent f b →
      ∀ p ∈ Global.line (lineId e) \ Global.line (lineId f),
        label p = wire (parent e (!a))) :
    ∃ S : Finset (Fin 13), 10 + (S.image label).card ≤ S.card := by
  classical
  by_cases hstar : ∃ v : ℕ, ∃ side : Fin 5 → Bool, ∀ e : Fin 5, parent e (side e) = v
  · obtain ⟨v, side, hs⟩ := hstar
    exact star_rank parent lineId hinj label wire hforce v side hs
  obtain ⟨a, ha⟩ := edge_has_nonleaf parent hconn 0
  obtain ⟨d, _, hd⟩ := core_neighbor_of_not_star parent hconn hstar (parent 0 a) ha
  by_cases htwo : ∃ e : Fin 5, e ≠ d ∧ CoreEdge parent e
  · obtain ⟨e, hed, he⟩ := htwo
    exact two_core_edges_rank parent lineId hinj hconn label wire hforce d e hed.symm hd he
  have hunique (e : Fin 5) (he : CoreEdge parent e) : e = d := by
    by_contra hed
    exact htwo ⟨e, hed, he⟩
  exact unique_core_rank parent lineId hinj hconn label wire hforce d hd hunique

end PEqualNP.Outside.L_meta_1024_aux.ParentRankCore
