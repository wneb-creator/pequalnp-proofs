import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.Collective

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024.OrOnly

abbrev V (C : Circuit) (x : Fin 13 → Bool) (i : ℕ) : Bool := value C x i

def readAt (C : Circuit) (x : Fin 13 → Bool) (k r : ℕ) : Bool :=
  if r < 13 + k then V C x r else false

def Good (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) : Prop :=
  ∀ k (hk : k < C.gates.length), C.gates[k].op = GateOp.and →
    V C z (13 + k) = false →
    pick k ∈ C.gates[k].inputs ∧ readAt C z k (pick k) = false

lemma good_exists (C : Circuit) (z : Fin 13 → Bool) : ∃ pick, Good C z pick := by
  classical
  have choice : ∀ k, ∃ r, ∀ (hk : k < C.gates.length),
      C.gates[k].op = GateOp.and → V C z (13 + k) = false →
      r ∈ C.gates[k].inputs ∧ readAt C z k r = false := by
    intro k
    by_cases hk : k < C.gates.length
    · by_cases hop : C.gates[k].op = GateOp.and
      · by_cases hz : V C z (13 + k) = false
        · have hn : ¬ ∀ r ∈ C.gates[k].inputs, r < 13 + k ∧ V C z r = true := by
            intro hh
            have ht := (and_value C k hk hop z).mpr hh
            change V C z (13 + k) = true at ht
            rw [hz] at ht
            exact Bool.noConfusion ht
          push_neg at hn
          obtain ⟨r, hr, hbad⟩ := hn
          refine ⟨r, fun _ _ _ => ⟨hr, ?_⟩⟩
          unfold readAt
          by_cases hlt : r < 13 + k
          · simp only [hlt, ite_true]
            have hnt : V C z r ≠ true := hbad hlt
            cases hv : V C z r <;> simp_all
          · simp [hlt]
        · exact ⟨0, fun _ _ h => (hz h).elim⟩
      · exact ⟨0, fun _ h _ => (hop h).elim⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose pick hp using choice
  exact ⟨pick, hp⟩

def Edge (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ (k : ℕ) (hk : k < C.gates.length), b = 13 + k ∧ a < b ∧ a ∈ C.gates[k].inputs ∧
    (C.gates[k].op = GateOp.or ∨ (C.gates[k].op = GateOp.and ∧ a = pick k)) ∧
    V C z a = false ∧ V C z b = false

def cone (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (o : ℕ) : Set ℕ :=
  {i | Relation.ReflTransGen (Edge C z pick) i o}

lemma edge_lt {C : Circuit} {z : Fin 13 → Bool} {pick : ℕ → ℕ} {a b : ℕ}
    (h : Edge C z pick a b) : a < b := by
  obtain ⟨k, hk, he, hlt, hrest⟩ := h
  exact hlt

lemma edge_false {C : Circuit} {z : Fin 13 → Bool} {pick : ℕ → ℕ} {a b : ℕ}
    (h : Edge C z pick a b) : V C z a = false ∧ V C z b = false := by
  obtain ⟨k, hk, he, hlt, hm, hop, ha, hb⟩ := h
  exact ⟨ha, hb⟩

lemma cone_false (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ) (o : ℕ)
    (ho : V C z o = false) {i : ℕ} (hi : i ∈ cone C z pick o) : V C z i = false := by
  rcases Relation.ReflTransGen.cases_head hi with rfl | ⟨j, hij, hjo⟩
  · exact ho
  · exact (edge_false hij).1

lemma positive_parent (C : Circuit) (z x : Fin 13 → Bool) (pick : ℕ → ℕ)
    (hpick : Good C z pick)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (i : ℕ) (hi : 13 ≤ i) (hz : V C z i = false) (hx : V C x i = true) :
    ∃ j, Edge C z pick j i ∧ V C x j = true := by
  have hil : i < 13 + C.gates.length := by
    by_contra hn
    have hf := missing_value C x i (by unfold Circuit.size; omega)
    change V C x i = false at hf
    rw [hf] at hx
    exact Bool.noConfusion hx
  let k := i - 13
  have hk : k < C.gates.length := by omega
  have he : i = 13 + k := by omega
  obtain hop | hop := hg C.gates[k] (List.getElem_mem hk)
  · have hz' : V C z (13 + k) = false := he ▸ hz
    have hx' : V C x (13 + k) = true := he ▸ hx
    obtain ⟨hm, hfalse⟩ := hpick k hk hop hz'
    obtain ⟨hlt, htrue⟩ := (and_value C k hk hop x).mp hx' (pick k) hm
    have hf : V C z (pick k) = false := by simpa [readAt, hlt] using hfalse
    exact ⟨pick k, ⟨k, hk, he, by omega, hm, Or.inr ⟨hop, rfl⟩, hf, hz⟩, htrue⟩
  · have hx' : V C x (13 + k) = true := he ▸ hx
    obtain ⟨j, hm, hlt, ht⟩ := (or_value C k hk hop x).mp hx'
    have hf : V C z j = false := by
      cases hv : V C z j
      · rfl
      · have hz' := (or_value C k hk hop z).mpr ⟨j, hm, hlt, hv⟩
        change V C z (13 + k) = true at hz'
        rw [← he, hz] at hz'
        exact Bool.noConfusion hz'
    exact ⟨j, ⟨k, hk, he, by omega, hm, Or.inl hop, hf, hz⟩, ht⟩

def Within (C : Circuit) (z : Fin 13 → Bool) (pick : ℕ → ℕ)
    (o : ℕ) (B : Set ℕ) (a b : ℕ) : Prop :=
  Edge C z pick a b ∧ a ∈ cone C z pick o ∧ b ∈ cone C z pick o ∧ a ∉ B ∧ b ∉ B

lemma path_avoiding (C : Circuit) (z x : Fin 13 → Bool) (pick : ℕ → ℕ)
    (hpick : Good C z pick)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (o : ℕ) (hz : V C z o = false) (hx : V C x o = true)
    (B : Set ℕ) (hB : ∀ i ∈ B, V C x i = false)
    (p : Fin 13) (hunique : ∀ q : Fin 13, z q = false → x q = true → q = p) :
    p.val ∈ cone C z pick o ∧ p.val ∉ B ∧
      Relation.ReflTransGen (Within C z pick o B) p.val o := by
  have walk : ∀ i, i ∈ cone C z pick o → V C x i = true →
      p.val ∈ cone C z pick o ∧ p.val ∉ B ∧
        Relation.ReflTransGen (Within C z pick o B) p.val i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hic hix
      have hib : i ∉ B := by
        intro hb
        rw [hB i hb] at hix
        exact Bool.noConfusion hix
      have hiz := cone_false C z pick o hz hic
      by_cases hir : i < 13
      · let q : Fin 13 := ⟨i, hir⟩
        have hqz : z q = false := by simpa only [← input_value C z q] using hiz
        have hqx : x q = true := by simpa only [← input_value C x q] using hix
        have hqp := hunique q hqz hqx
        have hip : i = p.val := congrArg Fin.val hqp
        subst i
        exact ⟨hic, hib, Relation.ReflTransGen.refl⟩
      · obtain ⟨j, hji, hjx⟩ := positive_parent C z x pick hpick hg i (by omega) hiz hix
        have hjc : j ∈ cone C z pick o :=
          (Relation.ReflTransGen.single hji).trans hic
        obtain ⟨hpc, hpb, hpj⟩ := ih j (edge_lt hji) hjc hjx
        have hjb : j ∉ B := by
          intro hb
          rw [hB j hb] at hjx
          exact Bool.noConfusion hjx
        exact ⟨hpc, hpb, hpj.tail ⟨hji, hjc, hic, hjb, hib⟩⟩
  exact walk o Relation.ReflTransGen.refl hx

lemma line_inter_nonempty : ∀ w v : Fin 13, (Global.line w ∩ Global.line v).Nonempty := by
  decide +kernel

lemma separating_card (w v p : Fin 13) (hwv : w ≠ v)
    (hp : p ∈ Global.line w) (hpv : p ∉ Global.line v) :
    (Global.line v ∪ (Global.line w).erase p).card = 6 := by
  have hcL : (Global.line w).card = 4 := Clamp.line_card w
  have hcM : (Global.line v).card = 4 := Clamp.line_card v
  have hi : (Global.line v ∩ Global.line w).card = 1 := by
    have hu := Global.line_intersection v w (Ne.symm hwv)
    have hl := Finset.card_pos.mpr (line_inter_nonempty v w)
    omega
  have he : Global.line v ∩ (Global.line w).erase p = Global.line v ∩ Global.line w := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, fun hqp => hpv (hqp ▸ h.1), h.2⟩
  have hc := Finset.card_union_add_card_inter (Global.line v) ((Global.line w).erase p)
  rw [he, hi, hcM, Finset.card_erase_of_mem hp, hcL] at hc
  omega

lemma collective_avoidance (C : Circuit) (w v : Fin 13) (oL oM : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x → V C x oL = Support.target w x)
    (hL : V C (Global.Zof (Global.line w)) oL = false)
    (hM : V C (Global.Zof (Global.line v)) oM = false)
    (pickL pickM : ℕ → ℕ)
    (hpickL : Good C (Global.Zof (Global.line w)) pickL)
    (hwv : w ≠ v) (p : Fin 13) (hp : p ∈ Global.line w) (hpv : p ∉ Global.line v) :
    p.val ∈ cone C (Global.Zof (Global.line w)) pickL oL ∧
    p.val ∉ cone C (Global.Zof (Global.line v)) pickM oM ∧
    Relation.ReflTransGen
      (Within C (Global.Zof (Global.line w)) pickL oL
        (cone C (Global.Zof (Global.line v)) pickM oM)) p.val oL := by
  let S := Global.line v ∪ (Global.line w).erase p
  let x := Support.fromZeros S
  have hcard : S.card = 6 := separating_card w v p hwv hp hpv
  have hb : Support.Band x := by
    right
    simpa only [x, Support.zeroSet_fromZeros] using hcard
  have hpx : x p = true := by simp [x, S, Support.fromZeros, hpv]
  have ht : Support.target w x = true := by
    exact decide_eq_true (show ∃ q ∈ Support.line w, x q = true from ⟨p, hp, hpx⟩)
  have hout : V C x oL = true := (hcorrect x hb).trans ht
  have hxy : ∀ q, x q = true → Global.Zof (Global.line v) q = true := by
    intro q hq
    simp only [x, Support.fromZeros, decide_eq_true_eq] at hq
    simp only [Global.Zof, decide_eq_true_eq]
    intro hqv
    exact hq (Finset.mem_union_left _ hqv)
  have hblocked : ∀ i ∈ cone C (Global.Zof (Global.line v)) pickM oM,
      V C x i = false := by
    intro i hi
    have hm := cone_false C _ pickM oM hM hi
    cases hv : V C x i
    · rfl
    · have hmt := mono C hg x (Global.Zof (Global.line v)) hxy i hv
      change V C (Global.Zof (Global.line v)) i = true at hmt
      rw [hm] at hmt
      exact Bool.noConfusion hmt
  apply path_avoiding C _ x pickL hpickL (fun g hg' => (hg g hg').1) oL hL hout
    _ hblocked p
  intro q hqz hqx
  have hqL : q ∈ Global.line w := by
    simpa only [Global.Zof, decide_eq_false_iff_not, not_not] using hqz
  have hqS : q ∉ S := by simpa only [x, Support.fromZeros, decide_eq_true_eq] using hqx
  by_contra hqp
  exact hqS (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hqp, hqL⟩))

end PEqualNP.Outside.L_meta_1024_aux.Collective
