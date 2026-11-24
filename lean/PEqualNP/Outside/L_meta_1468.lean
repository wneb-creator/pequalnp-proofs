import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1468

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

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma not_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.not) :
    ∃ r, ∀ x : Fin n → Bool, value C x (n + k) = false → r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  refine ⟨C.gates[k].inputs.headD 0, fun x h => ?_⟩
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop] at h
  rcases hin : C.gates[k].inputs with _ | ⟨a, tl⟩
  · rw [hin] at h
    simp [GateOp.eval] at h
  · rw [hin] at h
    by_cases ha : a < n + k
    · simpa [GateOp.eval, ha] using h
    · simp [GateOp.eval, ha] at h

lemma mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true)
    (hN : ∀ k, ∀ hk : k < C.gates.length,
      ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
      value C x (n + k) = true → value C y (n + k) = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact hN (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length)
    (hopk : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (hfank : C.gates[k].inputs.length ≤ 2) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases hopk with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs hfank
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hopM : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
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
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y (t - n) hk (hopM _ hk hm)
          (hfan _ (List.getElem_mem hk)) hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
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
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

lemma family {n : ℕ} {ι : Type*} (gates : List Gate)
    (hfan : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (T : Finset ι) (l : ι → Fin n → Bool) (y : Fin n → Bool) (o : ℕ)
    (hopM : ∀ k, ∀ hk : k < gates.length, Multi ⟨gates, 0⟩ T l y (n + k) →
      gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or)
    (ho : ∀ p ∈ T, Sv ⟨gates, 0⟩ l y p o)
    (hin : ∀ w, w < n → ¬ Multi ⟨gates, 0⟩ T l y w)
    (K : Finset (Fin gates.length))
    (hK : ∀ g : Fin gates.length, Multi ⟨gates, 0⟩ T l y (n + (g : ℕ)) →
      gates[(g : ℕ)].op = GateOp.or → gates[(g : ℕ)].inputs.length = 2 →
      (∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ T, value ⟨gates, 0⟩ (l p) r = true) → g ∈ K) :
    T.card ≤ K.card + 1 := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let W : Finset ℕ := Finset.image (fun g : Fin gates.length => n + (g : ℕ)) K
  have hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length := by
    intro w hc
    refine ⟨Nat.le_of_not_lt fun h => hin w h hc, ?_⟩
    by_contra hge
    obtain ⟨p, _, _, _, _, hsv, _⟩ := hc
    have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
    have h1 := hsv.1
    rw [hm] at h1
    exact Bool.noConfusion h1
  have h := frontier C T l y hfan hopM W
    (fun k hk hm hop hl hQ => Finset.mem_image.mpr ⟨(⟨k, hk⟩ : Fin gates.length), hK ⟨k, hk⟩ hm hop hl hQ, rfl⟩)
    hlen (n + C.gates.length) {o}
    (fun w _ hc => (hlen w hc).2) T (Finset.Subset.refl T)
    (fun p hp => ⟨o, Finset.mem_singleton_self o, ho p hp⟩)
  have h1 := Finset.card_filter_le W (· < n + C.gates.length)
  have h2 : W.card ≤ K.card := Finset.card_image_le
  rw [Finset.card_singleton] at h
  omega

def rowL {n m : ℕ} (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (p : Fin n) :
    Fin n → Bool :=
  fun v => decide (v ∈ R i p)

def coY {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : Fin n → Bool :=
  fun v => decide (v ∉ S i)

lemma kill {n m : ℕ} (gates : List Gate)
    (S : Fin m → Finset (Fin n)) (R : Fin m → Fin n → Finset (Fin n)) (i j : Fin m)
    (hN : ∀ k, ∀ hk : k < gates.length, ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) →
      ∀ a ∈ S i, value ⟨gates, 0⟩ (rowL R i a) (n + k) = false)
    (hint : (S i ∩ S j).card ≤ 1)
    (hnA : ¬ ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) (w : ℕ)
    (hi : Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) w)
    (hj : value ⟨gates, 0⟩ (coY S j) w = false) : False := by
  obtain ⟨p, hp, p', hp', hne, hs, hs'⟩ := hi
  have key : ∀ a ∈ S i, a ∉ S j → value ⟨gates, 0⟩ (rowL R i a) w = true → False := by
    intro a ha haj hv
    have := mono ⟨gates, 0⟩ (rowL R i a) (coY S j) (fun v hv => ?_)
      (fun k hk hop h => by rw [hN k hk hop a ha] at h; exact Bool.noConfusion h) w hv
    · rw [hj] at this
      exact Bool.noConfusion this
    · simp only [rowL, coY, decide_eq_true_eq] at hv ⊢
      intro hvj
      exact hnA ⟨a, Finset.mem_sdiff.mpr ⟨ha, haj⟩, ⟨v, Finset.mem_inter.mpr ⟨hv, hvj⟩⟩⟩
  by_cases hpj : p ∈ S j
  · by_cases hpj' : p' ∈ S j
    · exact hne (Finset.card_le_one.mp hint p (Finset.mem_inter.mpr ⟨hp, hpj⟩) p'
        (Finset.mem_inter.mpr ⟨hp', hpj'⟩))
    · exact key p' hp' hpj' hs'.1
  · exact key p hp hpj hs.1

def InK {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (i : Fin m) (g : Fin gates.length) : Prop :=
  Multi ⟨gates, 0⟩ (S i) (rowL R i) (coY S i) (n + (g : ℕ)) ∧
    gates[(g : ℕ)].op = GateOp.or ∧ gates[(g : ℕ)].inputs.length = 2 ∧
    ∀ r ∈ gates[(g : ℕ)].inputs, ∃ p ∈ S i, value ⟨gates, 0⟩ (rowL R i p) r = true


lemma t1461 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → 1 ≤ m → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q n m S R hq hm hcard hint hcov hR hno gates out j hg hj hone hout hNco hNrow
  set Rd := Finset.univ.filter
    (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs) with hRd
  classical
  have hnv : ∀ (k : ℕ) (hk : k < gates.length),
      ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) → k = (j : ℕ) := by
    intro k hk hop
    have hn : (gates.get ⟨k, hk⟩).op = GateOp.not := by
      rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
      · exact absurd (Or.inl h) hop
      · exact absurd (Or.inr h) hop
      · exact h
    exact congrArg Fin.val (hone ⟨k, hk⟩ hn)
  have hrow : ∀ (k : ℕ) (hk : k < gates.length),
      ¬ (gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or) → ∀ (i : Fin m), ∀ a ∈ S i,
      PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.rowL R i a) (n + k) = false := by
    intro k hk hop i a ha
    rw [hnv k hk hop]
    exact hNrow i a ha
  have hopM : ∀ (i : Fin m) (k : ℕ) (hk : k < gates.length),
      PEqualNP.Outside.L_meta_1468.Multi ⟨gates, 0⟩ (S i) (PEqualNP.Outside.L_meta_1468.rowL R i) (PEqualNP.Outside.L_meta_1468.coY S i) (n + k) →
      gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
    intro i k hk hmu
    by_contra hop
    obtain ⟨p, hp, _, _, _, hs, _⟩ := hmu
    have h1 := hs.1
    rw [hrow k hk hop i p hp] at h1
    exact Bool.noConfusion h1
  let K : Fin m → Finset (Fin gates.length) := fun i => Finset.univ.filter fun g =>
    PEqualNP.Outside.L_meta_1468.InK gates S R i g
  have hKq : ∀ i, q ≤ (K i).card := by
    intro i
    have h := PEqualNP.Outside.L_meta_1468.family (n := n) gates (fun g hgm => (hg g hgm).2) (S i)
      (PEqualNP.Outside.L_meta_1468.rowL R i) (PEqualNP.Outside.L_meta_1468.coY S i) (out i) (hopM i)
      (fun p hp => ⟨(hout i (PEqualNP.Outside.L_meta_1468.rowL R i p)).trans (decide_eq_true ⟨p, hp, by
          have h3 : p ∈ R i p ∩ S i := by rw [hR i p hp]; exact Finset.mem_singleton_self p
          simpa [PEqualNP.Outside.L_meta_1468.rowL] using (Finset.mem_inter.mp h3).1⟩),
        (hout i (PEqualNP.Outside.L_meta_1468.coY S i)).trans (decide_eq_false (by
          rintro ⟨v, hv, h⟩
          simp [PEqualNP.Outside.L_meta_1468.coY, hv] at h))⟩)
      (fun w hw hc => by
        obtain ⟨p, hp, p', hp', hne, hs1, hs2⟩ := hc
        have e : ∀ a ∈ S i, PEqualNP.Outside.L_meta_1468.Sv ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1468.rowL R i) (PEqualNP.Outside.L_meta_1468.coY S i) a w →
            (⟨w, hw⟩ : Fin n) = a := by
          intro a ha hsa
          have h1 : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1468.rowL R i a) ((⟨w, hw⟩ : Fin n) : ℕ) = true := hsa.1
          have h2 : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩
            (PEqualNP.Outside.L_meta_1468.coY S i) ((⟨w, hw⟩ : Fin n) : ℕ) = false := hsa.2
          rw [PEqualNP.Outside.L_meta_1468.input_value] at h1 h2
          simp only [PEqualNP.Outside.L_meta_1468.rowL, PEqualNP.Outside.L_meta_1468.coY,
            decide_eq_true_eq, decide_eq_false_iff_not, not_not] at h1 h2
          have h3 : (⟨w, hw⟩ : Fin n) ∈ R i a ∩ S i := Finset.mem_inter.mpr ⟨h1, h2⟩
          rw [hR i a ha] at h3
          exact Finset.mem_singleton.mp h3
        exact hne ((e p hp hs1).symm.trans (e p' hp' hs2)))
      (K i)
      (fun g hmu hop hl hQ => Finset.mem_filter.mpr ⟨Finset.mem_univ g, hmu, hop, hl, hQ⟩)
    have := hcard i
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j' ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j' → Disjoint (K i) (K j') := by
    intro i _ j' _ hij
    refine Finset.disjoint_left.mpr fun g hgi hgj => ?_
    have hmi := (Finset.mem_filter.mp hgi).2.1
    have hmj := (Finset.mem_filter.mp hgj).2.1
    have hyi : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.coY S i) (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmi
      exact hs.2
    have hyj : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.coY S j') (n + (g : ℕ)) = false := by
      obtain ⟨p, _, _, _, _, hs, _⟩ := hmj
      exact hs.2
    by_cases hA : ∃ p ∈ S i \ S j', (R i p ∩ S j').Nonempty
    · have hB : ¬ ∃ s ∈ S j' \ S i, (R j' s ∩ S i).Nonempty := fun hB => hno i j' hij ⟨hA, hB⟩
      exact PEqualNP.Outside.L_meta_1468.kill gates S R j' i (fun k hk hop => hrow k hk hop j')
        (by rw [Finset.inter_comm]; exact hint i j' hij) hB _ hmj hyi
    · exact PEqualNP.Outside.L_meta_1468.kill gates S R i j' (fun k hk hop => hrow k hk hop i) (hint i j' hij) hA _ hmi hyj
  obtain ⟨r, hr⟩ := PEqualNP.Outside.L_meta_1468.not_value (n := n) ⟨gates, 0⟩ (j : ℕ) j.isLt hj
  have hrco : ∀ i : Fin m, r < n + (j : ℕ) ∧ PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.coY S i) r = true :=
    fun i => hr (PEqualNP.Outside.L_meta_1468.coY S i) (hNco i)
  have hrn : n ≤ r := by
    by_contra hlt
    have hlt' : r < n := by omega
    obtain ⟨i, hi⟩ := hcov ⟨r, hlt'⟩
    have h1 : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.coY S i) ((⟨r, hlt'⟩ : Fin n) : ℕ) = true := (hrco i).2
    rw [PEqualNP.Outside.L_meta_1468.input_value] at h1
    simp [PEqualNP.Outside.L_meta_1468.coY, hi] at h1
  have hrj := (hrco ⟨0, hm⟩).1
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin gates.length, n + (g0 : ℕ) = r :=
    ⟨⟨r - n, by have := j.isLt; omega⟩, by simp only []; omega⟩
  have hg0j : g0 < j := Fin.lt_def.mpr (by omega)
  let N : Finset (Fin gates.length) := insert j (insert g0 Rd)
  have hNcard : N.card = Rd.card + 2 := by
    have h1 : g0 ∉ Rd := fun h => by
      have := (Finset.mem_filter.mp h).2.1
      exact absurd hg0j (not_lt.mpr this.le)
    have h2 : j ∉ insert g0 Rd := fun h => by
      rcases Finset.mem_insert.mp h with h | h
      · exact absurd hg0j (by rw [h]; exact lt_irrefl _)
      · exact absurd (Finset.mem_filter.mp h).2.1 (lt_irrefl _)
    rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
  have hND : Disjoint (Finset.univ.biUnion K) N := by
    refine Finset.disjoint_left.mpr fun g hgK hgN => ?_
    obtain ⟨i, _, hgi⟩ := Finset.mem_biUnion.mp hgK
    obtain ⟨hmu, hop, hl, hQ⟩ := (Finset.mem_filter.mp hgi).2
    rcases Finset.mem_insert.mp hgN with h | h
    · rw [h] at hop
      have hj' : gates[(j : ℕ)].op = GateOp.not := hj
      rw [hj'] at hop
      exact GateOp.noConfusion hop
    rcases Finset.mem_insert.mp h with h | h
    · obtain ⟨p, _, _, _, _, hs, _⟩ := hmu
      have h2 := hs.2
      rw [h, hg0, (hrco i).2] at h2
      exact Bool.noConfusion h2
    · have hin := (Finset.mem_filter.mp h).2.2
      obtain ⟨p, hp, hv⟩ := hQ _ hin
      have h2 : PEqualNP.Outside.L_meta_1468.value ⟨gates, 0⟩ (PEqualNP.Outside.L_meta_1468.rowL R i p) (n + (j : ℕ)) = false := hNrow i p hp
      rw [h2] at hv
      exact Bool.noConfusion hv
  have h1 := Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion K ∪ N))
  rw [Finset.card_union_of_disjoint hND, Finset.card_biUnion hdisj, Finset.card_univ,
    Fintype.card_fin, hNcard] at h1
  have h2 : ∑ i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hKq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega


def nxt (q k : ℕ) : ℕ := if k = q then 0 else k + 1

def prd (q k : ℕ) : ℕ := if k = 0 then q else k - 1

lemma prd_nxt (q k : ℕ) : prd q (nxt q k) = k := by
  by_cases h : k = q
  · simp [prd, nxt, h]
  · simp [prd, nxt, h]

lemma enum {n c : ℕ} (s : Finset (Fin n)) (v : Fin n) (hs : s.card = c) :
    ∃ g : ℕ → Fin n, (∀ k, k < c → g k ∈ s) ∧
      (∀ k k', k < c → k' < c → g k = g k' → k = k') ∧
      (∀ x, x ∈ s → ∃ k, k < c ∧ g k = x) := by
  classical
  refine ⟨fun k => if h : k < c then ((s.equivFinOfCardEq hs).symm ⟨k, h⟩ : Fin n) else v,
    ?_, ?_, ?_⟩
  · intro k hk
    simp only [hk, ↓reduceDIte]
    exact ((s.equivFinOfCardEq hs).symm ⟨k, hk⟩).2
  · intro k k' hk hk' h
    simp only [hk, hk', ↓reduceDIte] at h
    have h1 := (s.equivFinOfCardEq hs).symm.injective (Subtype.ext h)
    exact congrArg Fin.val h1
  · intro x hx
    refine ⟨((s.equivFinOfCardEq hs) ⟨x, hx⟩ : ℕ), ((s.equivFinOfCardEq hs) ⟨x, hx⟩).2, ?_⟩
    simp

lemma tp {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hi : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin m) (x y : Fin n) (hxi : x ∈ S i) (hxj : x ∈ S j)
    (hyi : y ∈ S i) (hyj : y ∈ S j) (hxy : x ≠ y) : i = j := by
  classical
  by_contra hne
  have h1 : 1 < (S i ∩ S j).card :=
    Finset.one_lt_card.mpr ⟨x, Finset.mem_inter.mpr ⟨hxi, hxj⟩, y,
      Finset.mem_inter.mpr ⟨hyi, hyj⟩, hxy⟩
  rw [hi i j hne] at h1
  omega

lemma main (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hc : ∀ i : Fin m, (S i).card = q + 1)
    (hi : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (hl : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i)
    (i0 : Fin m) (v : Fin n) (hv : v ∉ S i0) :
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  classical
  obtain ⟨g, hg1, hg2, hg3⟩ := enum (S i0) v (hc i0)
  have U : ∀ i, i ≠ i0 → ∀ k k', k < q + 1 → k' < q + 1 → g k ∈ S i → g k' ∈ S i →
      k = k' := by
    intro i hi0 k k' hk hk' h h'
    by_contra hkk
    have hne : g k ≠ g k' := fun h2 => hkk (hg2 k k' hk hk' h2)
    exact hi0 (tp S hi i i0 (g k) (g k') h (hg1 k hk) h' (hg1 k' hk') hne)
  have E : ∀ i, i ≠ i0 → ∃ k, k < q + 1 ∧ g k ∈ S i := by
    intro i hi0
    have h1 : 0 < (S i ∩ S i0).card := by rw [hi i i0 hi0]; omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp h1
    obtain ⟨k, hk, hgk⟩ := hg3 y (Finset.mem_inter.mp hy).2
    exact ⟨k, hk, hgk ▸ (Finset.mem_inter.mp hy).1⟩
  have hprd : ∀ k, k < q + 1 → prd q k < q + 1 := by
    intro k hk
    unfold prd
    split_ifs <;> omega
  have hnxt : ∀ k, k < q + 1 → nxt q k < q + 1 := by
    intro k hk
    unfold nxt
    split_ifs <;> omega
  have hex : ∀ i, ∃ x, (i = i0 → x = v) ∧
      (i ≠ i0 → v ∉ S i → ∀ k, k < q + 1 → g k ∈ S i → x = g (nxt q k)) ∧
      (i ≠ i0 → v ∈ S i → ∀ k, k < q + 1 → g k ∈ S i →
        x ∉ S i0 ∧ x ≠ v ∧ ∃ j', v ∈ S j' ∧ g (prd q k) ∈ S j' ∧ x ∈ S j') := by
    intro i
    by_cases hi0 : i = i0
    · exact ⟨v, fun _ => rfl, fun h => absurd hi0 h, fun h => absurd hi0 h⟩
    · obtain ⟨k, hk, hgk⟩ := E i hi0
      by_cases hvi : v ∈ S i
      · have hpk := hprd k hk
        have hne : v ≠ g (prd q k) := fun h => hv (h ▸ hg1 _ hpk)
        obtain ⟨j', hvj, hgj⟩ := hl v _ hne
        have hcard : ({v, g (prd q k)} : Finset (Fin n)).card < (S j').card := by
          have := Finset.card_le_two (a := v) (b := g (prd q k))
          rw [hc j']
          omega
        obtain ⟨x, hxj, hxn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        have hxv : x ≠ v := fun h => hxn (by simp [h])
        have hxg : x ≠ g (prd q k) := fun h => hxn (by simp [h])
        refine ⟨x, fun h => absurd h hi0, fun _ h => absurd hvi h,
          fun _ _ k' hk' hgk' => ?_⟩
        have hkk : k' = k := U i hi0 k' k hk' hk hgk' hgk
        subst hkk
        refine ⟨?_, hxv, j', hvj, hgj, hxj⟩
        intro hx0
        have h2 := tp S hi j' i0 x (g (prd q k')) hxj hx0 hgj (hg1 _ hpk) hxg
        exact hv (h2 ▸ hvj)
      · refine ⟨g (nxt q k), fun h => absurd h hi0, fun _ _ k' hk' hgk' => ?_,
          fun _ h => absurd h hvi⟩
        rw [U i hi0 k' k hk' hk hgk' hgk]
  choose b hb using hex
  have hA : ∀ j, j ≠ i0 → ¬ (b i0 ∈ S j ∧ b j ∈ S i0) := by
    rintro j hj ⟨h1, h2⟩
    rw [(hb i0).1 rfl] at h1
    obtain ⟨k, hk, hgk⟩ := E j hj
    exact ((hb j).2.2 hj h1 k hk hgk).1 h2
  have hBC : ∀ i j, i ≠ i0 → j ≠ i0 → v ∉ S i → v ∈ S j →
      ¬ (b i ∈ S j ∧ b j ∈ S i) := by
    rintro i j hi0 hj0 hvi hvj ⟨h1, h2⟩
    obtain ⟨k, hk, hgk⟩ := E i hi0
    obtain ⟨k', hk', hgk'⟩ := E j hj0
    rw [(hb i).2.1 hi0 hvi k hk hgk] at h1
    have e1 : nxt q k = k' := U j hj0 _ _ (hnxt k hk) hk' h1 hgk'
    obtain ⟨h0, _, j', hvj', hgj', hbj'⟩ := (hb j).2.2 hj0 hvj k' hk' hgk'
    have e2 : prd q k' = k := by
      rw [← e1]
      exact prd_nxt q k
    rw [e2] at hgj'
    have hne : b j ≠ g k := fun h => h0 (h ▸ hg1 k hk)
    have e3 := tp S hi i j' (b j) (g k) h2 hbj' hgk hgj' hne
    exact hvi (e3 ▸ hvj')
  refine ⟨b, ?_, ?_⟩
  · intro i hbi
    by_cases hi0 : i = i0
    · subst hi0
      rw [(hb i).1 rfl] at hbi
      exact hv hbi
    · obtain ⟨k, hk, hgk⟩ := E i hi0
      by_cases hvi : v ∈ S i
      · obtain ⟨_, hbv, j', hvj, hgj, hbj⟩ := (hb i).2.2 hi0 hvi k hk hgk
        have hij : i = j' := tp S hi i j' (b i) v hbi hbj hvi hvj hbv
        have hgi : g (prd q k) ∈ S i := hij ▸ hgj
        have e := U i hi0 (prd q k) k (hprd k hk) hk hgi hgk
        unfold prd at e
        split_ifs at e <;> omega
      · rw [(hb i).2.1 hi0 hvi k hk hgk] at hbi
        have e := U i hi0 (nxt q k) k (hnxt k hk) hk hbi hgk
        unfold nxt at e
        split_ifs at e <;> omega
  · rintro i j hij ⟨h1, h2⟩
    by_cases hi0 : i = i0
    · subst hi0
      exact hA j (Ne.symm hij) ⟨h1, h2⟩
    by_cases hj0 : j = i0
    · subst hj0
      exact hA i hij ⟨h2, h1⟩
    obtain ⟨k, hk, hgk⟩ := E i hi0
    obtain ⟨k', hk', hgk'⟩ := E j hj0
    by_cases hvi : v ∈ S i
    · by_cases hvj : v ∈ S j
      · obtain ⟨_, hbv, j1, hvj1, hgj1, hbj1⟩ := (hb i).2.2 hi0 hvi k hk hgk
        obtain ⟨_, hbv', j2, hvj2, hgj2, hbj2⟩ := (hb j).2.2 hj0 hvj k' hk' hgk'
        have e1 : j = j1 := tp S hi j j1 (b i) v h1 hbj1 hvj hvj1 hbv
        have e2 : i = j2 := tp S hi i j2 (b j) v h2 hbj2 hvi hvj2 hbv'
        have m1 : g (prd q k) ∈ S j := e1 ▸ hgj1
        have m2 : g (prd q k') ∈ S i := e2 ▸ hgj2
        have e3 := U j hj0 (prd q k) k' (hprd k hk) hk' m1 hgk'
        have e4 := U i hi0 (prd q k') k (hprd k' hk') hk m2 hgk
        unfold prd at e3 e4
        split_ifs at e3 e4 <;> omega
      · exact hBC j i hj0 hi0 hvj hvi ⟨h2, h1⟩
    · by_cases hvj : v ∈ S j
      · exact hBC i j hi0 hj0 hvi hvj ⟨h1, h2⟩
      · rw [(hb i).2.1 hi0 hvi k hk hgk] at h1
        rw [(hb j).2.1 hj0 hvj k' hk' hgk'] at h2
        have e3 := U j hj0 (nxt q k) k' (hnxt k hk) hk' h1 hgk'
        have e4 := U i hi0 (nxt q k') k (hnxt k' hk') hk h2 hgk
        unfold nxt at e3 e4
        split_ifs at e3 e4 <;> omega


lemma t1467 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  intro q n m S hq hc hi hl h
  obtain ⟨i0, v, hv⟩ := h
  exact PEqualNP.Outside.L_meta_1468.main q n m S hq hc hi hl i0 v hv

lemma glue : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q n m S hq hcard hint hline hoff gates out j hgate hjnot huniq heval hthr
  classical
  obtain ⟨b, hb, hmut⟩ := t1467 q n m S hq hcard hint hline hoff
  obtain ⟨j0, v0, hv0⟩ := hoff
  have hthree : ∀ i : Fin m, 1 < (S i).card := fun i => by rw [hcard i]; omega
  have hother : ∀ i : Fin m, ∃ k : Fin m, k ≠ i := by
    intro i
    by_cases h : i = j0
    · obtain ⟨a, ha, hne⟩ := Finset.exists_mem_ne (hthree i) v0
      obtain ⟨k, hk1, hk2⟩ := hline v0 a (Ne.symm hne)
      refine ⟨k, ?_⟩
      intro hki
      rw [hki, h] at hk1
      exact hv0 hk1
    · exact ⟨j0, Ne.symm h⟩
  have hcover : ∀ v : Fin n, ∃ i : Fin m, v ∈ S i := by
    intro v
    obtain ⟨a, _, hne⟩ := Finset.exists_mem_ne (hthree j0) v
    obtain ⟨k, hk1, _⟩ := hline v a (Ne.symm hne)
    exact ⟨k, hk1⟩
  refine t1461 q n m S (fun i p => {p, b i}) (by omega) j0.pos hcard
    (fun i k hik => (hint i k hik).le) hcover ?_ ?_ gates out j hgate hjnot huniq heval ?_ ?_
  · intro i p hp
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx | hx, hxS⟩
      · exact hx
      · rw [hx] at hxS
        exact absurd hxS (hb i)
    · intro hx
      rw [hx]
      exact ⟨Or.inl rfl, hp⟩
  · rintro i k hik ⟨⟨p, hp, x, hx⟩, ⟨s, hs, y, hy⟩⟩
    apply hmut i k hik
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx hy
    constructor
    · rcases hx with ⟨hx | hx, hxS⟩
      · rw [hx] at hxS
        exact absurd hxS (Finset.mem_sdiff.mp hp).2
      · rw [hx] at hxS
        exact hxS
    · rcases hy with ⟨hy | hy, hyS⟩
      · rw [hy] at hyS
        exact absurd hyS (Finset.mem_sdiff.mp hs).2
      · rw [hy] at hyS
        exact hyS
  · intro i
    apply hthr
    obtain ⟨k, hk⟩ := hother i
    have hsub : S k \ S i ⊆ Finset.univ.filter (fun v : Fin n => decide (v ∉ S i) = true) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, decide_eq_true (Finset.mem_sdiff.mp hv).2⟩
    have h1 := Finset.card_sdiff_add_card_inter (S k) (S i)
    have h2 := hcard k
    have h3 := hint k i hk
    have h4 := Finset.card_le_card hsub
    omega
  · intro i p hp
    apply hthr
    have hne : p ≠ b i := fun e => hb i (e ▸ hp)
    have hsub : ({p, b i} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun v : Fin n => decide (v ∈ ({p, b i} : Finset (Fin n))) = true) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, decide_eq_true hv⟩
    have h4 := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at h4
    exact h4

end PEqualNP.Outside.L_meta_1468

theorem PEqualNP.Outside.L_meta_1468 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1468.glue
