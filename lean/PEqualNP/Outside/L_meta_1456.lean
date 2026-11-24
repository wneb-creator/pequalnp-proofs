import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1456

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

def Below {n : ℕ} (C : Circuit) (x y : Fin n → Bool) : Prop :=
  (∀ v, x v = true → y v = true) ∧
  ∀ k, ∀ hk : k < C.gates.length,
    ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
    value C x (n + k) = true → value C y (n + k) = true

theorem below_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : Below C x y) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h.1 p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact h.2 (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


def Serves {n : ℕ} (C : Circuit) (l y : Fin n → Bool) (w : ℕ) : Prop :=
  value C l w = true ∧ value C y w = false

def Counted {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (z : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Serves C (l p) z w ∧ Serves C (l p') z w

-- An AND gate false at z reads an earlier wire false at z, true wherever the gate is true.
lemma and_input {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (z : Fin n → Bool)
    (hz : value C z (n + k) = false) :
    ∃ r : ℕ, ∀ x : Fin n → Bool, value C x (n + k) = true →
      r < n + k ∧ value C z r = false ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hzv := gate_value C z (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hzv
  rw [hzv] at hz
  simp only [hop, GateOp.eval] at hz
  have hna : ¬ ((C.gates[k].inputs.map fun r => if r < n + k then value C z r else false).all id
      = true) := by
    rw [hz]; exact Bool.false_ne_true
  rw [List.all_eq_true] at hna
  by_contra hcon
  apply hna
  intro b hb
  obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
  by_contra hb'
  apply hcon
  refine ⟨r, fun x hx => ?_⟩
  have hxv := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hxv
  rw [hxv] at hx
  simp only [hop, GateOp.eval, List.all_eq_true] at hx
  have hxr := hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩)
  by_cases h' : r < n + k
  · refine ⟨h', ?_, ?_⟩
    · simpa [h'] using hb'
    · simpa [h'] using hxr
  · simp [h'] at hxr

-- Frontier step: a counted OR gate is replaced by the wires it reads and paid for, a counted
-- AND gate is replaced by its one wire false at z, free of charge.
lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (z : Fin n → Bool)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ w, Counted C T l z w → ∃ k, ∃ hk : k < C.gates.length, w = n + k ∧
      (C.gates[k].op = GateOp.and ∨ (C.gates[k].op = GateOp.or ∧ w ∈ W)))
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Counted C T l z w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Serves C (l p) z w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Counted C T l z (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Counted C T l z t
    · obtain ⟨k, hk, htk, hop⟩ := hW t hex.2
      rcases hop with hand | ⟨hor, htW⟩
      · obtain ⟨p0, _, _, _, _, hsv0, _⟩ := hex.2
        have hzt : value C z (n + k) = false := by rw [← htk]; exact hsv0.2
        obtain ⟨r, hr⟩ := and_input C k hk hand z hzt
        have hrlt : r < n + k := (hr (l p0) (by rw [← htk]; exact hsv0.1)).1
        have hrz : value C z r = false := (hr (l p0) (by rw [← htk]; exact hsv0.1)).2.1
        have hrx : ∀ x : Fin n → Bool, value C x (n + k) = true → value C x r = true :=
          fun x hx => (hr x hx).2.2
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Counted C T l z w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · omega
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Serves C (l p) z w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            refine ⟨r, Finset.mem_insert_self _ _, hrx _ ?_, hrz⟩
            rw [← htk]; exact hsv.1
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      · have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := Or.inr hor
        let P : Finset ℕ := (C.gates[k].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[k].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[k].inputs
          have h3 := hfan _ (List.getElem_mem hk)
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Counted C T l z w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Serves C (l p) z w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            by_contra hcon
            have hy : value C z (n + k) = true := by
              refine gate_mono C k hk hop (l p) z (fun r hr hlt hv => ?_) (htk ▸ hsv.1)
              by_contra hne
              refine hcon ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
                (List.mem_filter.mpr ⟨hr, by simpa [htk] using hlt⟩)), hv, by simpa using hne⟩
            have hn := hsv.2
            rw [htk, hy] at hn
            exact Bool.noConfusion hn
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Counted C T l z w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

theorem main (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m)
    (hcard : (S i0).card = q + 1)
    (gates : List Gate) (out : Fin m → ℕ) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hout : ∀ (w : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true))
    (hnot : ∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) →
      Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true)
    (I : Finset (Fin gates.length))
    (hI : ∀ g : Fin gates.length, ((gates.get g).op = GateOp.or ∧
      (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) →
        Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x) = false) ∧
      2 ≤ ((S i0).filter (fun p => Circuit.eval ⟨gates, n + (g : ℕ)⟩
        (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) → g ∈ I) :
    q ≤ I.card := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let z : Fin n → Bool := fun v => decide (v ∉ S i0)
  let l : Fin n → Fin n → Bool := fun p v => decide (v = p)
  have hz : ∀ v ∈ S i0, z v = false := by
    intro v hv
    simp [z, hv]
  have hnotz : value C z (n + (j : ℕ)) = true := hnot z hz
  have hbelow : ∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → Below C x z := by
    intro x hx
    refine ⟨fun v hv => ?_, fun k hk hop _ => ?_⟩
    · have hv' : v ∉ S i0 := by
        intro h
        rw [hx v h] at hv
        exact Bool.noConfusion hv
      simp [z, hv']
    · have hk' : k < gates.length := hk
      have hn : (gates.get ⟨k, hk'⟩).op = GateOp.not := by
        rcases (hg _ (List.getElem_mem hk')).1 with h | h | h
        · exact absurd (Or.inl h) hop
        · exact absurd (Or.inr h) hop
        · exact h
      have e := hone ⟨k, hk'⟩ hn
      have ek : k = (j : ℕ) := congrArg Fin.val e
      rw [ek]
      exact hnotz
  let W : Finset ℕ := I.image (fun g : Fin gates.length => n + (g : ℕ))
  have hlen : ∀ w, Counted C (S i0) l z w → n ≤ w ∧ w < n + gates.length := by
    intro w hc
    obtain ⟨p, _, p', _, hne, hs1, hs2⟩ := hc
    constructor
    · by_contra hlt
      have hw : w < n := by omega
      have h1 : value C (l p) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hs1.1
      have h2 : value C (l p') ((⟨w, hw⟩ : Fin n) : ℕ) = true := hs2.1
      rw [input_value] at h1 h2
      have e1 : (⟨w, hw⟩ : Fin n) = p := by simpa [l] using h1
      have e2 : (⟨w, hw⟩ : Fin n) = p' := by simpa [l] using h2
      exact hne (e1.symm.trans e2)
    · by_contra hge
      have hm := missing_value C (l p) w (by unfold Circuit.size; change n + gates.length ≤ w; omega)
      have h1 := hs1.1
      rw [hm] at h1
      exact Bool.noConfusion h1
  have hW : ∀ w, Counted C (S i0) l z w → ∃ k, ∃ hk : k < C.gates.length, w = n + k ∧
      (C.gates[k].op = GateOp.and ∨ (C.gates[k].op = GateOp.or ∧ w ∈ W)) := by
    intro w hc
    obtain ⟨h1, h2⟩ := hlen w hc
    have hk : w - n < gates.length := by omega
    have hwk : w = n + (w - n) := by omega
    refine ⟨w - n, hk, hwk, ?_⟩
    obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
    rw [hwk] at hs1 hs2
    rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, (Finset.mem_image (s := I)
        (f := fun g : Fin gates.length => n + (g : ℕ))).mpr
        ⟨(⟨w - n, hk⟩ : Fin gates.length), hI ⟨w - n, hk⟩ ⟨h, ?_, ?_⟩, hwk.symm⟩⟩
      · intro x hx
        by_contra hx1
        have hx2 : value C x (n + (w - n)) = true := by
          change Circuit.eval ⟨gates, n + (w - n)⟩ (List.ofFn x) = true
          simpa using hx1
        have := below_mono C x z (hbelow x hx) _ hx2
        rw [hs1.2] at this
        exact Bool.noConfusion this
      · exact Finset.one_lt_card.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hs1.1⟩,
          p', Finset.mem_filter.mpr ⟨hp', hs2.1⟩, hne⟩
    · have e := hone ⟨w - n, hk⟩ h
      have ek : w - n = (j : ℕ) := congrArg Fin.val e
      have hs := hs1.2
      rw [ek, hnotz] at hs
      exact Bool.noConfusion hs
  have h := frontier C (S i0) l z (fun g hgm => (hg g hgm).2) W hW (n + gates.length)
    {out i0} (fun w _ hc => (hlen w hc).2) (S i0) (Finset.Subset.refl _)
    (fun p hp => ⟨out i0, Finset.mem_singleton_self _, by
      constructor
      · change Circuit.eval ⟨gates, out i0⟩ (List.ofFn (l p)) = true
        rw [hout]
        exact decide_eq_true ⟨p, hp, by simp [l]⟩
      · change Circuit.eval ⟨gates, out i0⟩ (List.ofFn z) = false
        rw [hout]
        refine decide_eq_false ?_
        rintro ⟨v, hv, hvt⟩
        rw [hz v hv] at hvt
        exact Bool.noConfusion hvt⟩)
  have h1 := Finset.card_filter_le W (· < n + gates.length)
  have h2 : W.card ≤ I.card := Finset.card_image_le (s := I)
    (f := fun g : Fin gates.length => n + (g : ℕ))
  rw [Finset.card_singleton] at h
  omega

end PEqualNP.Outside.L_meta_1456

theorem PEqualNP.Outside.L_meta_1456 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    (S i0).card = q + 1 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x) = false) ∧
      2 ≤ ((S i0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) → g ∈ I) → q ≤ I.card :=
  fun q n m S i0 hcard gates out j hg _ hone hout hnot I hI =>
    PEqualNP.Outside.L_meta_1456.main q n m S i0 hcard gates out j hg hone hout hnot I hI
