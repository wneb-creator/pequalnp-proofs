import PEqualNP.Outside.L_meta_10760

namespace PEqualNP.Outside.L_meta_10760.Counted

-- Source-only candidate: numeric algorithms and certificates are unchanged.
-- MFt remembers the NOT budget through the first-original-wire-gate phase.
def MFt (R : Nat → Nat) (m T k t : Nat) (Fs : Set Nat) (S : Finset Nat) : Prop :=
  ∀ s ∈ Fs, ∀ q < k, ¬ LTR m T q t
    (C m (insert s ({x | R x ≠ 0} ∪ (S : Set Nat))))

def P1t (R : Nat → Nat) (P : List Nat) (l m T : Nat) (Fs : Set Nat)
    (f : Nat → Nat → Nat → List W → Bool) : Prop :=
  ∀ (k t z : Nat) (v : List W) (S : Finset Nat),
    f k t z v = false → StOk P T l k z v S →
    (∀ w ∈ v, w.r = R w.s) → ∀ k' ≤ k,
    Live Z0 m T k' t S → MW R m T k' S → MFt R m T k' t Fs S → False

lemma LTR.to_sol {m T q u : Nat} {S : Set Nat} (h : LTR m T q u S) :
    Sol Z0 m T q S := by
  obtain ⟨k, hk, t, ht, hbal, V, hV, hl⟩ := h
  exact hl.sol.mono hk hV

lemma live_ltr {m T k t : Nat} {S : Finset Nat} {Q : Set Nat}
    (h : Live Z0 m T k t S) (hs : (S : Set Nat) ⊆ Q) : LTR m T k t Q :=
  ⟨k, le_rfl, t, le_rfl, le_rfl, S, hs, h⟩

lemma MFt.of_full {R : Nat → Nat} {m T k t : Nat} {Fs : Set Nat} {S : Finset Nat}
    (h : MF R m T k Fs S) : MFt R m T k t Fs S := by
  intro f hf q hq hs
  exact h f hf q hq (LTR.to_sol hs)

lemma MFt.bi {R : Nat → Nat} {m T k t a b : Nat} {Fs : Set Nat} {d : Bool}
    {S S1 : Finset Nat} (h : MFt R m T (k + 1) t Fs S)
    (hb : Bi Z0 d a b S S1) : MFt R m T k t Fs S1 := by
  intro f hf q hq hs
  refine h f hf (q + 1) (by omega) (LTR.bi
    (d := d) (a := a) (b := b)
    (Or.inl (Or.inr (Or.inr hb.sub.1)))
    (Or.inl (Or.inr (Or.inr hb.sub.2.1)))
    (hs.mono le_rfl le_rfl le_rfl ?_))
  rw [← Set.insert_union, ← Set.insert_union]
  exact step_sub hb.sub.2.2

lemma MFt.gate {R : Nat → Nat} {m T k t a b : Nat} {Fs : Set Nat} {d : Bool}
    {S S1 : Finset Nat} (h : MFt R m T (k + 1) t Fs S)
    (hb : Bi Z0 d a b S S1) (hl : Live Z0 m T k t S1)
    (hg : op d a b ∈ Fs) : False := by
  refine h _ hg k (by omega) (live_ltr hl ?_)
  intro x hx
  have hx' := hb.sub.2.2 hx
  simp only [Finset.mem_insert] at hx'
  rcases hx' with rfl | hx'
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inr hx'))

section
variable {R : Nat → Nat}
theorem phase_step_t (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {P : List ℕ} {m T l k k' t : ℕ} {f : ℕ → List W → Bool} {v : List W} {S : Finset ℕ} {fm fh : ℕ} {Fs : Set ℕ}
    (hrep : Rep v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MFt R m T k' t Fs S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hA : ¬ Min R m T k' t S)
    (hB : ∀ (d : Bool) (a c : W) (S1 : Finset ℕ) (k0 : ℕ), a ∈ v → c ∈ v → a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → k' = k0 + 1 → Bi Z0 d a.s c.s S S1 → Live Z0 m T k0 t S1 →
      fbit fm fh (op d a.s c.s) = false → ∃ z' r, f z' r = false ∧ StOk P T l (k - 1) z' r S1 ∧ ∀ w ∈ r, (w.s = op d a.s c.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r)
    (hF : ∀ (z' : ℕ) (r : List W) (S1 : Finset ℕ), f z' r = false → StOk P T l (k - 1) z' r S1 → (∀ w ∈ r, w.r = R w.s) → ∀ k0 ≤ k - 1, Live Z0 m T k0 t S1 →
      MW R m T k0 S1 → MFt R m T k0 t Fs S1 → False) : False := by
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact hA ⟨hlR, (hmW.min hl).2⟩
  · obtain ⟨wa, hwa, rfl⟩ := hrep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hrep.mem.1 hb.sub.2.1
    have hnf : fbit fm fh (op d wa.s wb.s) = false := by
      by_contra hc
      exact hFb.gate hb hl1 (hfb d wa.s wb.s hb.1 ha hb' (by simpa using hc))
    obtain ⟨z', r, hf, hst, hmem⟩ := hB d wa wb S1 k0 hwa hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb') rfl hb hl1 hnf
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF z' r S1 hf hst ?_ k0 (by omega) hl1 (hmW.bi hb) (hFb.bi hb)
    intro w hw
    rcases hmem w hw with ⟨e1, e2⟩ | ⟨w', hw', e1, e2⟩
    · rw [e1, e2, hfr]
    · rw [← e1, ← e2]; exact hcod w' hw'
end

section sound
variable {R : Nat → Nat} {P : List Nat} {l m g np T : Nat} (X : Ctx P l m g np T)
include X
lemma one_sound_t (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh fu : ℕ} {Fs : Set ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hF : P1t R P l m T Fs f) {k t z : ℕ} {v : List W} {S : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MFt R m T k' t Fs S) (hKP : KP Z0 m T k' t S v κ κ2)
    (h2 : mv (look l m g np fu) l m g np k t z v κ κ2 = false)
    (h1 : ∀ x y, x ∈ S → y ∈ S → x ≠ y → R x ≠ 0 → R y ≠ 0 → ∃ go : (L_meta_10760.X → L_meta_10760.X → Bool) → List L_meta_10760.X → Bool,
      node1 (f (k - 1) t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 go = false ∧
      ∀ h xs, go h xs = false → ∀ a c : L_meta_10760.X, a ∈ xs → c ∈ xs → a.w.r ≠ 0 → c.w.r ≠ 0 → a.s = x → c.s = y → h a c = false ∨ h c a = false) : False := by
  refine phase_step_t hR2 (P := P) (l := l) (f := f (k - 1) t) (fm := fm) (fh := fh) (Fs := Fs) hs.rep hcod hk hl hmW hFb hfb ?_ ?_ ?_
  · intro hm
    exact mv_sound X hR (look_sound X hR fu) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk hm hKP.toR
  · intro d a c S1 k0 ha hc hne har hcr e hb hl1 hnf
    subst e
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hm := hmW.min hl
    obtain ⟨go, hg1, hg2⟩ := h1 a.s c.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (hs.rep.mem.2 ⟨c, hc, rfl⟩) hne (by rw [← hcod a ha]; exact har) (by rw [← hcod c hc]; exact hcr)
    have hsz := (hb.min hl1 hm.2).size
    refine nodeH_bi X hs hm (by omega) rfl rfl (by omega) hb hl1 hKP ?_ ?_ hg1
    · intro a' c' oa oc ka kc kb x1 y1 e hh
      rw [e] at hh ⊢
      exact mid1_false hnf hh
    · intro h xs hgo hxs a' c' ha' hc' hav hcv ea ec eax ecy
      refine hg2 h xs hgo a' c' ha' hc' ?_ ?_ eax ecy
      · have : a'.w = a := hs.rep.inj hav ha (by rw [← ea, eax])
        rw [this]; exact har
      · have : c'.w = c := hs.rep.inj hcv hc (by rw [← ec, ecy])
        rw [this]; exact hcr
  · intro z' r S1 hf hst hcod' k0 hk0 hl1 hmW1 hFb1
    exact hF _ _ _ _ _ hf hst hcod' k0 hk0 hl1 hmW1 hFb1
theorem look1_sound_t (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K : ℕ} {Fs : Set ℕ}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) : ∀ fuel : ℕ, P1t R P l m T Fs (look1 l m g np fm fh K fuel) := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW hFb
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 => Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K fuel k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin := hmW.min hl
      obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_f hy
      rw [st_eq] at hy1
      refine one_sound_t X hR hR2 hfb ih hs hcod hlen hk hl hmW hFb hKP hy2 fun x y hx hy hne hxr hyr => ⟨pairsS, hy1, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
      exact pairs_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e]))
theorem topC_sound_t (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g np fm fh K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) (hFb : MFt R m T k' t Fs S) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have hmin := hmW.min hl
  obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))) : Bool) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, (hFy _).symm.trans h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  refine one_sound_t X hR hR2 hfb (look1_sound_t X hR hR2 (K := K) hfb K) hs hcod (un p0 hp0).1 hk hl hmW hFb hKP (fu := k) ?_ ?_
  · have := (or_f (un p0 hp0).2).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro x y hx hy hne hxr hyr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((x + y) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    have h3 := (or_f (un p hpM).2).1
    rw [st_eq] at h3
    refine ⟨_, h3, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
    exact pairsC_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e])) (by rw [ea, ec]; exact hpb)
end sound

-- The old unrestricted interface remains derivable for Q tables, ownership,
-- and the unconditional lower bound. Final integration replaces topC_ok's body.
theorem topC_ok_unrestricted : TopOk topC := by
  intro P l m g np T X R hR hR2 fm fh K k t z v S M Fs hM h hs hcod k' hk hl hmW hfb hFb
  exact topC_sound_t X hR hR2 hM h hs hcod hk hl hmW hfb (MFt.of_full hFb)

def TopOkT (top : TopT) : Prop :=
  ∀ {P : List Nat} {l m g np T : Nat}, Ctx P l m g np T →
    ∀ {R : Nat → Nat},
    (∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b) →
    (∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) →
    ∀ {fm fh K k t z : Nat} {v : List W} {S : Finset Nat}
      {M : List (Nat × Nat)} {Fs : Set Nat}, mFull M = true →
    (∀ p ∈ M, top l m g np fm fh K p.1 p.2 k t z v = false) →
    StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
    ∀ {k' : Nat}, k' ≤ k → Live Z0 m T k' t S →
    MW R m T k' S →
    (∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 →
      fbit fm fh (op d x y) = true → op d x y ∈ Fs) →
    MFt R m T k' t Fs S → False

theorem topC_ok_t : TopOkT topC := by
  intro P l m g np T X R hR hR2 fm fh K k t z v S M Fs hM h hs hcod k' hk hl hmW hfb hFb
  exact topC_sound_t X hR hR2 hM h hs hcod hk hl hmW hfb hFb

def ImpT (E : List Gt) (Z L u : Nat) : Prop :=
  ∀ q < L, ¬ LTR (mz Z) (tz Z) q u (C (mz Z) (WZ E Z))

lemma ltr_add {e : Gt} {E : List Gt} {Z q u : Nat} {S : Set Nat}
    (hS : S ⊆ C (mz Z) (WZ E Z))
    (hs : LTR (mz Z) (tz Z) q u (insert (tw e &&& mz Z) S)) :
    LTR (mz Z) (tz Z) (q + 1) u (C (mz Z) (WZ E Z)) := by
  refine LTR.bi (d := e.1) (raw_avail E e.2.1 Z) (raw_avail E e.2.2 Z)
    (hs.mono le_rfl le_rfl le_rfl ?_)
  rw [← and_op]
  exact Set.insert_subset_insert hS

lemma forb_ok_t {E : List (Bool × ℕ × ℕ)} {f : Bool × ℕ × ℕ} {Z L u : ℕ} (hE : E.length ≤ 1) (hf : ImpT [f] Z (L + E.length) u) :
    ∀ q < L, ¬ LTR (mz Z) (tz Z) q u (C (mz Z) (insert (tw f &&& mz Z) (WZ E Z))) := by
  intro q hq hs
  have hsub : C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z)) ⊆ C (mz Z) (WZ [f] Z) := by
    rintro x ((rfl | hx) | hx)
    · exact Or.inl ⟨tw f, by simp [rawL], rfl⟩
    · exact Or.inl (WZ_nil_sub _ _ hx)
    · exact Or.inr hx
  match E, hE, hf, hs with
  | [], _, hf, hs => exact hf q (by simpa using hq) (hs.mono le_rfl le_rfl le_rfl hsub)
  | [e], _, hf, hs =>
    refine hf (q + 1) (by simpa using hq) (ltr_add (e := e) (S := C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z))) hsub (hs.mono le_rfl le_rfl le_rfl ?_))
    rintro x ((rfl | ⟨w, hw, rfl⟩) | hx)
    · exact Or.inr (Or.inl (Or.inl rfl))
    · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inr (Or.inl (Or.inr ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩))
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)

lemma reject_live_t {top : TopT} (htop : TopOkT top)
    {E F : List (Bool × Nat × Nat)} {Q : List (Nat × Nat)} {fb : Nat × Nat}
    {Z K k t : Nat} {S : Finset Nat}
    (hk : k ≤ K) (hK : K ≤ 15) (hE1 : E.length ≤ 1)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hfb : fb = (1, 0) ∨ (Z = 0 ∧ fbOk E F fb = true))
    (hF : ∀ e ∈ F, ImpT [e] 0 (k + E.length) t)
    (hmin : Imp E Z k)
    (hS : (S : Set Nat) ⊆ C (mz Z) (WZ E Z))
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hpw : pwr E Z = 0 ∨ pwr E Z ∈ S)
    (M : List (Nat × Nat)) (hMf : mFull M = true)
    (hchk : ∀ p ∈ M, chkG top E Q fb Z K t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  obtain ⟨a1, a2⟩ := avl_spec (mz Z) (rawL E)
  set v := ((avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S))).map (mkW (PZ Q)) with hv
  have hsub : v.Sublist ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := List.filter_sublist.map _
  have hvs : v.map W.s = (avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S)) := by
    rw [hv, List.map_map]; exact List.map_id _
  have hnd : (v.map W.s).Nodup := by
    rw [hvs]
    exact (a1.sublist List.filter_sublist).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, hvs, List.mem_filter, a2]
    constructor
    · rintro ⟨_, hx⟩; simpa using hx
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      exact ⟨⟨fun e => h0 (e ▸ hx), fun e => h1 (e ▸ hx), w, hw, rfl⟩, by simpa using hx⟩
  have hvm : ∀ w ∈ v, ∃ x ∈ rawL E, w = mkW (PZ Q) (x &&& mz Z) := by
    intro w hw
    rw [hv, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    obtain ⟨_, _, x, hx, rfl⟩ := (a2 s).1 (List.mem_of_mem_filter hs)
    exact ⟨x, hx, rfl⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := hvm w hw; exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; exact wire_good hx Z
  have hd0 : ∀ w ∈ v, w.d = 0 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; rfl
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_, ⟨fun j => (PZ Q).getD j 0, fun j _ => PZ_lt Q j, npOf_eq _, fun j _ _ => Nat.and_self _⟩⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hA : ∀ j < (PZ Q).length, Acc ((PZ Q).getD j 0) (tz Z) K (K - (Q.getD j (0, K)).2) (fun _ => 0) S := by
    intro j hj
    obtain ⟨e1, e2⟩ := hPget j hj
    rw [e1]
    exact Acc.start (L := (Q.getD j (0, K)).2) (hno _ e2) subset_rfl (by omega)
  have hle := cnt_le X (D := fun _ _ => 0) hrep hwok hA hm (by omega)
  have hz : pL (Q.map fun e => 16 + (K - e.2)) - sumc v = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2) - cnt v j) := by
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hst : StOk (PZ Q) (tz Z) (lz Z) K (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v S := by
    rw [hz]
    exact StOk.start hrep hwok hgood (by omega) (fun j _ => by omega) hd0 hA
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, show pos t = pos' t by cases t <;> simp [pos, pos'], hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble (lnW v) (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    rw [lnW_eq]; change v.length ≤ K + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, top (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chkG, st_eq, pre_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startG, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => top (lz Z) (mz Z) _ (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t z r) (fun h => rfl) rfl hst hm (by omega) h3
  have hW : {x | RZ E Z x ≠ 0} ∪ (S : Set ℕ) = WZ E Z := by rw [RZ_set]; exact Set.union_eq_self_of_subset_right hSW
  refine htop X (RZ_RR E Z) (RZ_R2 E Z) (Fs := {s | ∃ f ∈ F, s = tw f &&& mz Z ∧ Z = 0}) hMf all hst hcod (by omega) hl ?_ ?_ ?_
  · intro q hq hs
    rw [hW] at hs
    exact hmin q hq hs
  · intro d x y hxy hx hy hbit
    rcases hfb with rfl | ⟨rfl, hfb⟩
    · rw [fbit_triv] at hbit; simp at hbit
    · obtain ⟨f, hf, e⟩ := fbOk_spec hfb (RZ_mem hx) (RZ_mem hy) hxy hbit
      exact ⟨f, hf, e, rfl⟩
  · rintro s ⟨f, hf, rfl, rfl⟩ q hq hs
    rw [hW] at hs
    exact forb_ok_t hE1 (hF f hf) q (by omega) hs

lemma gate_bound_t {e : Gt} {F : List Gt} {Q : List (Nat × Nat)}
    {fb : Nat × Nat} {M : List (Nat × Nat)}
    (h0 : Imp [] 0 13)
    (hp : pOk 0 Q = true) (hQ : ∀ x ∈ Q, Imp [e] x.1 x.2)
    (hfb : fbOk [e] F fb = true)
    (hF : ∀ f ∈ F, ImpT [f] 0 13 1)
    (hM : mFull M = true)
    (hc : ∀ p ∈ M, chkT topC [e] Q fb 0 12 [1] p.1 p.2 = false) :
    ImpT [e] 0 13 1 := by
  intro q hq hs
  have hmin : Imp [e] 0 12 := impB h0
  have hq12 : 12 ≤ q := by
    by_contra hn
    exact hmin q (by omega) (LTR.to_sol hs)
  have heq : q = 12 := by omega
  subst q
  obtain ⟨S, hS, hL⟩ := LTR.exact_counts hmin hs
  have hpw : pwr [e] 0 = 0 ∨ pwr [e] 0 ∈ S := by
    by_contra hn
    push_neg at hn
    refine h0 12 (by omega) (hL.sol.mono le_rfl ?_)
    intro x hx
    rcases hS hx with ⟨w, hw, rfl⟩ | hx'
    · simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simpa only [rawL, List.map_nil, List.append_nil] using hw, rfl⟩
      · exact False.elim (hn.2 hx)
    · exact Or.inr hx'
  refine reject_live_t topC_ok_t (F := F) (K := 12) (fb := fb)
    (by omega) (by decide) (by simp) hp hQ (Or.inr ⟨rfl, hfb⟩)
    (by simpa using hF) hmin hS hL hpw M hM ?_
  intro p hpM
  exact chkT_chk (hc p hpM) 1 (by simp)

lemma ty_imp_shards_t {gs : List Gt} {raw : List (Nat × Nat)} {i : Nat} {e : Gt}
    {own cs : List Nat} {fb : Nat × Nat} {M : List (Nat × Nat)}
    (hr : ∀ x ∈ raw, Imp [] x.1 x.2)
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2)
    (hshape : okTy gs raw 12 i e own cs fb [List.range 13] = true)
    (hM : mFull M = true)
    (hchecks : ∀ p ∈ M,
      chkT topC [e] (tabE e own (pick raw cs)) fb 0 12 [1] p.1 p.2 = false)
    (h0 : Imp [] 0 13) (hF : ∀ f ∈ gs.take i, ImpT [f] 0 13 1) :
    ImpT [e] 0 13 1 := by
  simp only [okTy, Bool.and_eq_true] at hshape
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hshape
  exact gate_bound_t h0 a4 (rootQ hr ho) a5 hF hM hchecks

lemma reject_one_shards_t {F : List Gt} {Q : List (Nat × Nat)}
    {fb : Nat × Nat} {M : List (Nat × Nat)}
    (hQ : ∀ e ∈ Q, Imp [] e.1 e.2) (hp : pOk 0 Q = true)
    (hfb : fbOk [] F fb = true) (hF : ∀ e ∈ F, ImpT [e] 0 13 1)
    (hmin : Imp [] 0 13) (hM : mFull M = true)
    (hc : ∀ p ∈ M, chkT topC [] Q fb 0 13 [1] p.1 p.2 = false) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S := by
  intro S hS hL
  refine reject_live_t topC_ok_t (K := 13) (F := F) (fb := fb)
    (by decide) (by decide) (by decide) hp hQ (Or.inr ⟨rfl, hfb⟩)
    (by simpa using hF) hmin hS hL (Or.inl rfl) M hM ?_
  intro p hpM
  exact chkT_chk (hc p hpM) 1 (by simp)

lemma live_rho_ltr {p : List Nat} {m T k t : Nat} {S : Finset Nat}
    (h : Live Z0 m T k t S) :
    LTR (rho p m) (rho p T) k t (rho p '' (S : Set Nat)) := by
  induction h with
  | stop => exact LTR.done (Set.mem_image_of_mem _ (by simp))
  | @un k t a U hl ih =>
    refine LTR.un (a := rho p a)
      (Set.mem_image_of_mem _ (by simp))
      (ih.mono le_rfl le_rfl le_rfl ?_)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [rho_xor]; exact Or.inl rfl
    · exact Or.inr ⟨x, by simp [hx], rfl⟩
  | @bi k t d a b U hab hal hl ih =>
    refine LTR.bi (d := d) (a := rho p a) (b := rho p b)
      (Set.mem_image_of_mem _ (by simp)) (Set.mem_image_of_mem _ (by simp))
      (ih.mono le_rfl le_rfl le_rfl ?_)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [rho_op]; exact Or.inl rfl
    · exact Or.inr ⟨x, by simp [hx], rfl⟩

lemma LTR.rho {p : List Nat} {m T q u : Nat} {S : Set Nat}
    (h : LTR m T q u S) : LTR (rho p m) (rho p T) q u (rho p '' S) := by
  obtain ⟨k, hk, t, ht, hbal, V, hV, hl⟩ := h
  refine (live_rho_ltr (p := p) hl).mono hk ht hbal ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hV hx, rfl⟩

theorem impT_symZ {p : List ℕ} {g : ℕ → ℕ} {E E' : List (Bool × ℕ × ℕ)} {Z Z' L u : ℕ} (hs : symOk p Z Z' = true)
    (hr : ∀ v < 7, rho p (rawP.getD v 0) = rawP.getD (g v) 0)
    (hE : ∀ e ∈ E, e.2.1 < 7 ∧ e.2.2 < 7 ∧ ∃ e' ∈ E', tw e' = tw (gimg g e)) (h : ImpT E' Z' L u) : ImpT E Z L u := by
  simp only [symOk, Bool.and_eq_true] at hs
  have hm : rho p (mz Z) = mz Z' := Nat.eq_of_beq_eq_true hs.1
  have hT : rho p (tz Z) = tz Z' := Nat.eq_of_beq_eq_true hs.2
  intro q hq hsol
  have h2 := LTR.rho (p := p) hsol
  rw [hm, hT] at h2
  refine h q hq (h2.mono le_rfl le_rfl le_rfl ?_)
  rintro x ⟨y, hy, rfl⟩
  rcases hy with ⟨w, hw, rfl⟩ | hy
  · rw [rho_and, hm]
    simp only [rawL, List.mem_append, List.mem_map] at hw
    rcases hw with hw | ⟨e, he, rfl⟩
    · obtain ⟨v, hv8, rfl⟩ := mem_rawP hw
      rw [hr v hv8]
      exact raw_avail E' (g v) Z'
    · obtain ⟨h1, h2, e', he', htw⟩ := hE e he
      have : rho p (tw e) = tw e' := by
        rw [htw]
        simp only [tw, gimg]
        rw [rho_op, hr _ h1, hr _ h2]
      rw [this]
      exact Or.inl ⟨tw e', by simp only [rawL, List.mem_append, List.mem_map]; exact Or.inr ⟨e', he', rfl⟩, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h0 | h0
    · rw [h0, rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h0, hm]; exact Or.inr (Set.mem_insert_of_mem _ rfl)

lemma impT_gate_congr {e e' : Gt} {Z L u : Nat} (he : tw e = tw e')
    (h : ImpT [e'] Z L u) : ImpT [e] Z L u := by
  unfold ImpT WZ rawL at h ⊢
  simpa only [List.map_cons, List.map_nil, he] using h

lemma impT_gate_swap {d : Bool} {a b Z L u : Nat}
    (h : ImpT [(d, a, b)] Z L u) : ImpT [(d, b, a)] Z L u := by
  apply impT_gate_congr (h := h)
  cases d <;> simp [tw, op, Nat.and_comm, Nat.or_comm]

lemma sym_bound_t (d : Bool) (a b : Nat) (ha : a < 7) (hb : b < 7)
    {L u : Nat} (h : ImpT [(d, autoV a, autoV b)] 0 L u) :
    ImpT [(d, a, b)] 0 L u := by
  exact impT_symZ auto_sym auto_raw (symE1 ⟨ha, hb⟩ (by simp [gimg])) h

end PEqualNP.Outside.L_meta_10760.Counted
