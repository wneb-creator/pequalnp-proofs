import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18099

open PEqualNP.AndCount

abbrev V := Fin 42

abbrev rel (a b : V) : Prop :=
  a.val < 21 ∧ 21 ≤ b.val ∧ (b.val + 21 - a.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)

abbrev adj (a b : V) : Prop := rel a b ∨ rel b a

def graph : SimpleGraph V := SimpleGraph.fromRel rel

def color (v : V) : Bool := decide (v.val < 21)

lemma edge_iff (a b : V) : graph.Adj a b ↔ adj a b := by
  rw [graph, SimpleGraph.fromRel_adj]
  refine and_iff_right_of_imp ?_
  rintro (h | h) rfl <;> omega

lemma adj_symm {a b : V} : adj a b → adj b a := Or.symm

lemma adj_color {a b : V} (h : adj a b) : color a ≠ color b := by
  rcases h with h | h
  · simp [color, h.1, not_lt_of_ge h.2.1]
  · simp [color, h.1, not_lt_of_ge h.2.1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma common : ∀ u v : V, color u = color v → ∃ w : V, adj u w ∧ adj v w := by
  decide +kernel

def commonSet (u v : V) : Finset V :=
  Finset.univ.filter fun w => adj u w ∧ adj v w

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma common_le : ∀ u v : V, u ≠ v → (commonSet u v).card ≤ 1 := by
  decide +kernel

lemma common_unique {u v a b : V} (hne : u ≠ v)
    (ha : adj u a ∧ adj v a) (hb : adj u b ∧ adj v b) : a = b :=
  Finset.card_le_one.mp (common_le u v hne) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
    _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)

def edges : Finset (V × V) := Finset.univ.filter fun e => rel e.1 e.2

def star (v : V) : Finset (V × V) :=
  edges.filter fun e => e.1 = v ∨ e.2 = v

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma edges_card : edges.card = 105 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma star_card : ∀ v : V, (star v).card ≤ 5 := by
  decide +kernel

def covers (T : Finset V) : Prop :=
  ∀ ⦃a b⦄, adj a b → a ∈ T ∨ b ∈ T

lemma stars_cover {T : Finset V} (hT : covers T) : T.biUnion star = edges := by
  ext e
  constructor
  · intro he
    obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hv).1
  · intro he
    rcases hT (Or.inl (Finset.mem_filter.mp he).2) with ha | hb
    · exact Finset.mem_biUnion.mpr ⟨e.1, ha, Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨e.2, hb, Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩⟩

lemma cover_ge {T : Finset V} (hT : covers T) : 21 ≤ T.card := by
  have h := Finset.card_biUnion_le_card_mul T star 5 (fun v _ => star_card v)
  rw [stars_cover hT, edges_card] at h
  omega

lemma overlap {T : Finset V} (hT : covers T) (hcard : T.card = 21)
    {u v : V} (hu : u ∈ T) (hv : v ∈ T) (hadj : rel u v) : False := by
  let R := (T.erase u).biUnion star
  have hne : u ≠ v := fun h => adj_color (Or.inl hadj) (congrArg color h)
  have he : (u, v) ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  have hr : (u, v) ∈ R := Finset.mem_biUnion.mpr
    ⟨v, Finset.mem_erase.mpr ⟨hne.symm, hv⟩, Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩⟩
  have hpos : 0 < (star u ∩ R).card :=
    Finset.card_pos.mpr ⟨(u, v), Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩, hr⟩⟩
  have hR := Finset.card_biUnion_le_card_mul (T.erase u) star 5 (fun w _ => star_card w)
  rw [Finset.card_erase_of_mem hu, hcard] at hR
  have hR' : R.card ≤ 100 := hR
  have hsplit : star u ∪ R = edges := by
    rw [← stars_cover hT]
    change star u ∪ (T.erase u).biUnion star = T.biUnion star
    rw [← Finset.biUnion_insert, Finset.insert_erase hu]
  have hadd := Finset.card_union_add_card_inter (star u) R
  rw [hsplit, edges_card] at hadd
  have := star_card u
  omega

lemma cover_uniform {T : Finset V} (hT : covers T) (hcard : T.card = 21)
    {u v : V} (hu : u ∈ T) (hv : v ∈ T) : color u = color v := by
  have independent {a b : V} (ha : a ∈ T) (hb : b ∈ T) : ¬ adj a b := by
    rintro (h | h)
    · exact overlap hT hcard ha hb h
    · exact overlap hT hcard hb ha h
  by_contra hn
  obtain ⟨w, hw⟩ := common v v rfl
  have cw := adj_color hw.1
  have hsame : color u = color w := by
    cases hu' : color u <;> cases hv' : color v <;> cases hw' : color w <;>
      simp_all
  obtain ⟨z, huz, hwz⟩ := common u w hsame
  have hz : z ∉ T := fun hz => independent hu hz huz
  have hwT : w ∈ T := (hT hwz).resolve_right hz
  exact independent hv hwT hw.1

def raw (C : AndCountCircuit 42) (i : Fin C.size) (s : Bool) : Finset V :=
  if s then C.leftVars i else C.rightVars i

def part (C : AndCountCircuit 42) (i : Fin C.size) (s t : Bool) : Finset V :=
  (raw C i s).filter fun v => color v = t

lemma hit_transfer (C : AndCountCircuit 42) (U W : Finset V)
    (h : ∀ i s v, v ∈ raw C i s → v ∈ U → ∃ w ∈ raw C i s, w ∈ W) :
    ∀ d i, C.gateValFuel U d i = true → C.gateValFuel W d i = true := by
  intro d
  induction d with
  | zero => simp [AndCountCircuit.gateValFuel]
  | succ d ih =>
    intro i hi
    have transfer (s : Bool) (F : Finset (Fin C.size))
        (hs : AndCountCircuit.sideTrue U (raw C i s) F i (C.gateValFuel U d) = true) :
        AndCountCircuit.sideTrue W (raw C i s) F i (C.gateValFuel W d) = true := by
      unfold AndCountCircuit.sideTrue at hs ⊢
      rw [decide_eq_true_eq] at hs ⊢
      rcases hs with ⟨v, hv, hvU⟩ | ⟨j, hj, hji, hjU⟩
      · exact Or.inl (h i s v hv hvU)
      · exact Or.inr ⟨j, hj, hji, ih j hjU⟩
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨transfer true _ hi.1, transfer false _ hi.2⟩

def negative (b : V) : Finset V :=
  insert b (Finset.univ.filter fun w => color w ≠ color b ∧ ¬ adj w b)

lemma negative_independent (b : V) :
    ∀ a ∈ negative b, ∀ c ∈ negative b, ¬ adj a c := by
  intro a ha c hc h
  rcases Finset.mem_insert.mp ha with rfl | ha <;>
    rcases Finset.mem_insert.mp hc with rfl | hc
  · exact adj_color h rfl
  · exact (Finset.mem_filter.mp hc).2.2 (adj_symm h)
  · exact (Finset.mem_filter.mp ha).2.2 h
  · have ha' := (Finset.mem_filter.mp ha).2.1
    have hc' := (Finset.mem_filter.mp hc).2.1
    exact adj_color h ((Bool.eq_not_of_ne ha').trans (Bool.eq_not_of_ne hc').symm)

lemma separating (C : AndCountCircuit 42) (hcomp : C.Computes graph) (hout : C.outVars = ∅)
    {a b : V} (hab : adj a b) :
    ∃ i s, a ∈ part C i s (color a) ∧ ∀ w ∈ part C i s (color a), adj w b := by
  classical
  by_contra! hn
  have accept : C.eval {a, b} = true :=
    (hcomp _).mpr ⟨a, by simp, b, by simp, (edge_iff _ _).mpr hab⟩
  have hban : C.eval (negative b) ≠ true := by
    intro hb
    obtain ⟨u, hu, v, hv, h⟩ := (hcomp _).mp hb
    exact negative_independent b u hu v hv ((edge_iff _ _).mp h)
  apply hban
  have swap (i : Fin C.size) (s : Bool) (v : V)
      (hv : v ∈ raw C i s) (hv' : v ∈ ({a, b} : Finset V)) :
      ∃ w ∈ raw C i s, w ∈ negative b := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with hv' | hv'
    · subst v
      have ha : a ∈ part C i s (color a) := Finset.mem_filter.mpr ⟨hv, rfl⟩
      obtain ⟨w, hw, hno⟩ := hn i s ha
      obtain ⟨hw', hc⟩ := Finset.mem_filter.mp hw
      have hne : color w ≠ color b := hc.trans_ne (adj_color hab)
      exact ⟨w, hw', Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, not_or.mpr hno⟩)⟩
    · subst v
      exact ⟨b, hv, Finset.mem_insert_self _ _⟩
  unfold AndCountCircuit.eval at accept ⊢
  rw [decide_eq_true_eq, hout] at accept ⊢
  rcases accept with ⟨v, hv, _⟩ | ⟨i, hi, he⟩
  · exact (Finset.notMem_empty v hv).elim
  · exact Or.inr ⟨i, hi, hit_transfer C _ _ swap C.size i he⟩

noncomputable def owner (B : Finset V) : V := by
  classical
  exact if h : ∃ v, B = {v} then Classical.choose h
    else if h : ∃ b, ∀ w ∈ B, adj w b then Classical.choose h else 0

lemma owner_single {B : Finset V} {v : V} (he : B = {v}) : owner B = v := by
  classical
  unfold owner
  have hx : ∃ w, B = {w} := ⟨v, he⟩
  rw [dif_pos hx]
  have hc := Classical.choose_spec hx
  exact (Finset.singleton_injective (he.symm.trans hc)).symm

lemma owner_multi {B : Finset V} (hB : 1 < B.card)
    {b : V} (hb : ∀ w ∈ B, adj w b) : owner B = b := by
  classical
  have hns : ¬ ∃ v, B = {v} := by
    rintro ⟨v, rfl⟩
    simp at hB
  have hex : ∃ c, ∀ w ∈ B, adj w c := ⟨b, hb⟩
  unfold owner
  rw [dif_neg hns, dif_pos hex]
  have hc := Classical.choose_spec hex
  have hex' : ∃ u ∈ B, ∃ v ∈ B, u ≠ v := by
    by_contra! h
    exact (not_le_of_gt hB) (Finset.card_le_one.mpr h)
  obtain ⟨u, hu, v, hv, hn⟩ := hex'
  exact common_unique hn ⟨hc u hu, hc v hv⟩ ⟨hb u hu, hb v hv⟩

lemma centered {B : Finset V} {a b : V} (ha : a ∈ B) (hb : ∀ w ∈ B, adj w b) :
    a = owner B ∨ b = owner B := by
  by_cases hB : 1 < B.card
  · exact Or.inr (owner_multi hB hb).symm
  · left
    exact (owner_single (Finset.eq_singleton_iff_unique_mem.mpr
      ⟨ha, fun w hw => Finset.card_le_one.mp (by omega) w hw a ha⟩)).symm

abbrev Slot (C : AndCountCircuit 42) := Fin C.size × Bool × Bool

def valid (B : Finset V) : Prop := B.Nonempty ∧ ∃ b : V, ∀ w ∈ B, adj w b

noncomputable def slots (C : AndCountCircuit 42) : Finset (Slot C) := by
  classical
  exact Finset.univ.filter fun x => valid (part C x.1 x.2.1 x.2.2)

noncomputable def slotsColor (C : AndCountCircuit 42) (t : Bool) : Finset (Slot C) :=
  (slots C).filter fun x => x.2.2 = t

noncomputable def centers (C : AndCountCircuit 42) (t : Bool) : Finset V :=
  (slotsColor C t).image fun x => owner (part C x.1 x.2.1 x.2.2)

lemma centers_cover (C : AndCountCircuit 42) (hc : C.Computes graph) (ho : C.outVars = ∅)
    (t : Bool) : covers (centers C t) := by
  classical
  have forward (a b : V) (hab : adj a b) (he : color a = t) :
      a ∈ centers C t ∨ b ∈ centers C t := by
    obtain ⟨i, s, ha, hb⟩ := separating C hc ho hab
    have hmem : (i, s, color a) ∈ slotsColor C t :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨a, ha⟩, b, hb⟩⟩, he⟩
    have hown : owner (part C i s (color a)) ∈ centers C t :=
      Finset.mem_image.mpr ⟨_, hmem, rfl⟩
    rcases centered ha hb with h | h
    · exact Or.inl (h ▸ hown)
    · exact Or.inr (h ▸ hown)
  intro a b hab
  by_cases he : color a = t
  · exact forward a b hab he
  · have hb := adj_color hab
    have he' : color b = t := by
      cases ha : color a <;> cases hbb : color b <;> cases t <;> simp_all
    exact (forward b a (adj_symm hab) he').symm

def clean (C : AndCountCircuit 42) (i : Fin C.size) : Prop :=
  ∀ u ∈ C.leftVars i, ∀ v ∈ C.rightVars i, graph.Adj u v

noncomputable def gateSlots (C : AndCountCircuit 42) (i : Fin C.size) : Finset (Slot C) :=
  (slots C).filter fun x => x.1 = i

lemma gateSlots_le (C : AndCountCircuit 42) (i : Fin C.size) : (gateSlots C i).card ≤ 4 := by
  have inj : Set.InjOn (fun x : Slot C => x.2) ↑(gateSlots C i) := by
    intro a ha b hb he
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) he
  have h := Finset.card_le_univ ((gateSlots C i).image fun x => x.2)
  rwa [Finset.card_image_of_injOn inj, Fintype.card_prod, Fintype.card_bool] at h

lemma gateSlots_clean (C : AndCountCircuit 42) (i : Fin C.size) (hc : clean C i) :
    (gateSlots C i).card ≤ 2 := by
  classical
  have left (x : Slot C) (hx : x ∈ gateSlots C i) :
      x.1 = i ∧ (part C i x.2.1 x.2.2).Nonempty := by
    obtain ⟨h, he⟩ := Finset.mem_filter.mp hx
    exact ⟨he, he ▸ (Finset.mem_filter.mp h).2.1⟩
  have key {f : Slot C → Bool} (hinj : Set.InjOn f ↑(gateSlots C i)) :
      (gateSlots C i).card ≤ 2 := by
    have h := Finset.card_le_univ ((gateSlots C i).image f)
    rwa [Finset.card_image_of_injOn hinj, Fintype.card_bool] at h
  by_cases hL : (C.leftVars i).Nonempty
  · by_cases hR : (C.rightVars i).Nonempty
    · obtain ⟨u, hu⟩ := hL
      obtain ⟨v, hv⟩ := hR
      apply key (f := fun x => x.2.1)
      intro x hx y hy hs
      change x.2.1 = y.2.1 at hs
      obtain ⟨hxg, a, ha⟩ := left x hx
      obtain ⟨hyg, b, hb⟩ := left y hy
      have cc : x.2.2 = y.2.2 := by
        obtain ⟨ha', hac⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb', hbc⟩ := Finset.mem_filter.mp hb
        rw [← hac, ← hbc]
        rw [← hs] at hb'
        cases hside : x.2.1
        · have h1 := adj_color ((edge_iff _ _).mp (hc u hu a (by simpa [raw, hside] using ha')))
          have h2 := adj_color ((edge_iff _ _).mp (hc u hu b (by simpa [raw, hside] using hb')))
          exact (Bool.eq_not_of_ne h1.symm).trans (Bool.eq_not_of_ne h2.symm).symm
        · have h1 := adj_color ((edge_iff _ _).mp (hc a (by simpa [raw, hside] using ha') v hv))
          have h2 := adj_color ((edge_iff _ _).mp (hc b (by simpa [raw, hside] using hb') v hv))
          exact (Bool.eq_not_of_ne h1).trans (Bool.eq_not_of_ne h2).symm
      exact Prod.ext (hxg.trans hyg.symm) (Prod.ext hs cc)
    · apply key (f := fun x => x.2.2)
      have onlyLeft (x : Slot C) (hx : x ∈ gateSlots C i) : x.2.1 = true := by
        obtain ⟨_, w, hw⟩ := left x hx
        cases hs : x.2.1
        · exact (hR ⟨w, by simpa [raw, hs] using (Finset.mem_filter.mp hw).1⟩).elim
        · rfl
      intro x hx y hy hc'
      exact Prod.ext ((left x hx).1.trans (left y hy).1.symm)
        (Prod.ext ((onlyLeft x hx).trans (onlyLeft y hy).symm) hc')
  · apply key (f := fun x => x.2.2)
    have onlyRight (x : Slot C) (hx : x ∈ gateSlots C i) : x.2.1 = false := by
      obtain ⟨_, w, hw⟩ := left x hx
      cases hs : x.2.1
      · rfl
      · exact (hL ⟨w, by simpa [raw, hs] using (Finset.mem_filter.mp hw).1⟩).elim
    intro x hx y hy hc'
    exact Prod.ext ((left x hx).1.trans (left y hy).1.symm)
      (Prod.ext ((onlyRight x hx).trans (onlyRight y hy).symm) hc')

lemma slots_bound (C : AndCountCircuit 42) (d : Fin C.size)
    (hclean : ∀ i, i ≠ d → clean C i) :
    (slots C).card ≤ 2 * (C.size - 1) + (gateSlots C d).card := by
  classical
  let I : Finset (Fin C.size) := Finset.univ.erase d
  have heq : slots C = I.biUnion (gateSlots C) ∪ gateSlots C d := by
    ext x
    constructor
    · intro hx
      by_cases he : x.1 = d
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, he⟩))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr
          ⟨x.1, Finset.mem_erase.mpr ⟨he, Finset.mem_univ _⟩, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩))
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_filter.mp hi).1
      · exact (Finset.mem_filter.mp hx).1
  have hb := Finset.card_biUnion_le_card_mul I (gateSlots C) 2
    (fun i hi => gateSlots_clean C i (hclean i (Finset.mem_erase.mp hi).1))
  have hI : I.card = C.size - 1 := by simp [I]
  rw [hI] at hb
  rw [heq]
  have hu := Finset.card_union_le (I.biUnion (gateSlots C)) (gateSlots C d)
  omega

lemma one_dirty (C : AndCountCircuit 42) (hc : C.Computes graph) (ho : C.outVars = ∅)
    (hd : ∀ i, Disjoint (C.leftVars i) (C.rightVars i)) (hs : C.size ≤ 20)
    (d : Fin C.size) (hclean : ∀ i, i ≠ d → clean C i) :
    ∀ s t, (part C d s t).card = 1 := by
  classical
  have hcov (t : Bool) := centers_cover C hc ho t
  have hlo (t : Bool) := cover_ge (hcov t)
  have himg (t : Bool) : (centers C t).card ≤ (slotsColor C t).card := Finset.card_image_le
  have hloT := hlo true
  have hloF := hlo false
  have himgT := himg true
  have himgF := himg false
  have hsum : (slotsColor C true).card + (slotsColor C false).card = (slots C).card := by
    have h := Finset.card_filter_add_card_filter_not (s := slots C) (p := fun x => x.2.2 = true)
    simpa only [slotsColor, Bool.not_eq_true] using h
  have hS := slots_bound C d hclean
  have hD := gateSlots_le C d
  have ha : (centers C true).card = 21 := by omega
  have hb : (centers C false).card = 21 := by omega
  have all : ∀ s t, valid (part C d s t) := by
    have hcard : (gateSlots C d).card = 4 := by omega
    let f : Slot C → Bool × Bool := Prod.snd
    have hi : Set.InjOn f ↑(gateSlots C d) := by
      intro x hx y hy hxy
      exact Prod.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm) hxy
    have heq : (gateSlots C d).image f = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injOn hi, hcard]
      decide
    intro s t
    have hmem : (s, t) ∈ (gateSlots C d).image f := heq.symm ▸ Finset.mem_univ _
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hmem
    obtain ⟨hx', hxg⟩ := Finset.mem_filter.mp hx
    have he' : x = (d, s, t) := Prod.ext hxg he
    rw [he'] at hx'
    exact (Finset.mem_filter.mp hx').2
  have used (t : Bool) : (slotsColor C t).card = 21 := by
    cases t <;> omega
  have inj (t : Bool) :
      Set.InjOn (fun x : Slot C => owner (part C x.1 x.2.1 x.2.2)) ↑(slotsColor C t) := by
    apply Finset.injOn_of_card_image_eq
    change (centers C t).card = _
    rw [used]
    cases t <;> assumption
  have owner_mem (s t : Bool) : owner (part C d s t) ∈ centers C t := by
    exact Finset.mem_image.mpr ⟨(d, s, t),
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, all s t⟩, rfl⟩, rfl⟩
  have centers_card (t : Bool) : (centers C t).card = 21 := by cases t <;> assumption
  intro s t
  have result (r : Bool) : (part C d r t).card = 1 ∨
      ∃ b, owner (part C d r t) = b ∧ ∀ w ∈ part C d r t, adj w b := by
    have hpos := Finset.card_pos.mpr (all r t).1
    by_cases he : (part C d r t).card = 1
    · exact Or.inl he
    · obtain ⟨b, hb'⟩ := (all r t).2
      exact Or.inr ⟨b, owner_multi (by omega) hb', hb'⟩
  have singleton_color (r : Bool) (h : (part C d r t).card = 1) :
      color (owner (part C d r t)) = t := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    rw [owner_single ha]
    have hm : a ∈ part C d r t := ha.symm ▸ Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hm).2
  have multi_color (r : Bool) (b : V) (hb' : ∀ w ∈ part C d r t, adj w b) : color b ≠ t := by
    obtain ⟨w, hw⟩ := (all r t).1
    exact fun he => adj_color (hb' w hw) ((Finset.mem_filter.mp hw).2.trans he.symm)
  have huni := cover_uniform (hcov t) (centers_card t) (owner_mem true t) (owner_mem false t)
  rcases result true with hT | ⟨b, eB, hb'⟩ <;> rcases result false with hF | ⟨c, eC, hc'⟩
  · cases s <;> assumption
  · apply (multi_color false c hc').elim
    rw [← eC, ← huni]
    exact singleton_color true hT
  · apply (multi_color true b hb').elim
    rw [← eB, huni]
    exact singleton_color false hF
  · have hcolor : color b = color c := by simpa only [eB, eC] using huni
    have full (r : Bool) (v : V) (ev : owner (part C d r t) = v)
        (hvt : color v ≠ t) {w : V} (hv : adj w v) : w ∈ part C d r t := by
      have hwt : color w = t :=
        (Bool.eq_not_of_ne (adj_color hv)).trans (Bool.eq_not_of_ne hvt.symm).symm
      obtain ⟨j, k, hmem, hval⟩ := separating C hc ho hv
      have hx : (j, k, color w) ∈ slotsColor C t :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨⟨w, hmem⟩, v, hval⟩⟩, hwt⟩
      have hy : (d, r, t) ∈ slotsColor C t :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, all r t⟩, rfl⟩
      have hx' : owner (part C j k (color w)) ∈ centers C t :=
        Finset.mem_image.mpr ⟨_, hx, rfl⟩
      have hv' : v ∈ centers C t := ev ▸ owner_mem r t
      have eq : owner (part C j k (color w)) = v := by
        rcases centered hmem hval with h | h
        · have hcol := cover_uniform (hcov t) (centers_card t) hx' hv'
          rw [← h, hwt] at hcol
          exact (hvt hcol.symm).elim
        · exact h.symm
      have hslot : (j, k, color w) = (d, r, t) := inj t hx hy (eq.trans ev.symm)
      have hi := congrArg (fun x : Slot C => x.1) hslot
      have hs' := congrArg (fun x : Slot C => x.2.1) hslot
      have ht' := congrArg (fun x : Slot C => x.2.2) hslot
      change j = d at hi
      change k = r at hs'
      change color w = t at ht'
      simpa only [hi, hs', ht'] using hmem
    obtain ⟨w, hbw, hcw⟩ := common b c hcolor
    have hL := (Finset.mem_filter.mp (full true b eB (multi_color true b hb') (adj_symm hbw))).1
    have hR := (Finset.mem_filter.mp (full false c eC (multi_color false c hc') (adj_symm hcw))).1
    exact (Finset.disjoint_left.mp (hd d) (by simpa [raw] using hL) (by simpa [raw] using hR)).elim

lemma bare_bound (C : AndCountCircuit 42) (d : Fin C.size)
    (hs : ∀ s t, (part C d s t).card = 1) (S : Finset (V × V))
    (he : ∀ e ∈ S, e.1.val < 21 ∧ graph.Adj e.1 e.2 ∧
      (e.1 ∈ C.leftVars d ∧ e.2 ∈ C.rightVars d ∨ e.2 ∈ C.leftVars d ∧ e.1 ∈ C.rightVars d)) :
    S.card ≤ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hs true true)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (hs false false)
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hs false true)
  obtain ⟨d', hd'⟩ := Finset.card_eq_one.mp (hs true false)
  let T : Finset (V × V) := {(a, b), (c, d')}
  have hT : S ⊆ T := by
    intro e hm
    obtain ⟨hpc, hadj, hbare⟩ := he e hm
    have hpoint : color e.1 = true := by simp [color, hpc]
    have hline : color e.2 = false := by
      apply Bool.eq_false_of_not_eq_true
      intro hx
      exact adj_color ((edge_iff _ _).mp hadj) (hpoint.trans hx.symm)
    rcases hbare with ⟨hL, hR⟩ | ⟨hL, hR⟩
    · have hl : e.1 ∈ part C d true true := Finset.mem_filter.mpr ⟨hL, hpoint⟩
      have hr : e.2 ∈ part C d false false := Finset.mem_filter.mpr ⟨hR, hline⟩
      rw [ha, Finset.mem_singleton] at hl
      rw [hb, Finset.mem_singleton] at hr
      exact Finset.mem_insert.mpr (Or.inl (Prod.ext hl hr))
    · have hl : e.2 ∈ part C d true false := Finset.mem_filter.mpr ⟨hL, hline⟩
      have hr : e.1 ∈ part C d false true := Finset.mem_filter.mpr ⟨hR, hpoint⟩
      rw [hd', Finset.mem_singleton] at hl
      rw [hc, Finset.mem_singleton] at hr
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext hr hl)))
  have hh := Finset.card_insert_le (a, b) ({(c, d')} : Finset (V × V))
  rw [Finset.card_singleton] at hh
  exact (Finset.card_le_card hT).trans hh

end PEqualNP.Outside.L_meta_18099


theorem PEqualNP.Outside.L_meta_18099 : have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x3 : Fin x2.size) (x4 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x4.1 ∈ x2.leftVars x3 ∧ x4.2 ∈ x2.rightVars x3 ∨ x4.2 ∈ x2.leftVars x3 ∧ x4.1 ∈ x2.rightVars x3; have x3 : (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x3.size → Prop := fun (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x4 : Fin x3.size) => ∀ x5 ∈ x3.leftVars x4, ∀ x7 ∈ x3.rightVars x4, x1.Adj x5 x7; ∀ (x4 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x4.WellFormed → x4.Computes x1 → x4.outVars = ∅ → (∀ (x8 : Fin x4.size) (x9 : Fin (42 : ℕ)), x4.gateVal {x9} x8 = Bool.false) → (∀ (x9 : Fin x4.size), Disjoint (x4.leftVars x9) (x4.rightVars x9)) → x4.size ≤ (20 : ℕ) → (∃ x11 ∉ x4.outGates, ¬x3 x4 x11 ∧ (∀ (x12 : Fin x4.size), x12 ≠ x11 → x3 x4 x12) ∧ ∃ (x12 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))), (10 : ℕ) ≤ x12.card ∧ ∀ x13 ∈ x12, ↑x13.1 < (21 : ℕ) ∧ x1.Adj x13.1 x13.2 ∧ x2 x4 x11 x13 ∧ ∀ (x15 : Fin x4.size), x15 ≠ x11 → ¬x2 x4 x15 x13) → False := by
  intro G bare isClean C _ hcomp hout _ hdisj hsize he
  obtain ⟨d, _, _, hclean, S, hlarge, hS⟩ := he
  have hs := PEqualNP.Outside.L_meta_18099.one_dirty C hcomp hout hdisj hsize d hclean
  have hb := PEqualNP.Outside.L_meta_18099.bare_bound C d hs S
    (fun e he => ⟨(hS e he).1, (hS e he).2.1, (hS e he).2.2.1⟩)
  omega

