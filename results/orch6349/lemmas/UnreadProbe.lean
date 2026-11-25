import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349.LRAT.Link

abbrev Model := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)
abbrev Model.op (M : Model) := M.1
abbrev Model.s1 (M : Model) := M.2.1
abbrev Model.s2 (M : Model) := M.2.2.1
abbrev Model.so (M : Model) := M.2.2.2.1
abbrev Model.w (M : Model) := M.2.2.2.2
@[simp] theorem Model.op_pair (o : ℕ → ℕ) (z : (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)) :
  Model.op (o,z) = o := rfl
@[simp] theorem Model.s1_pair (o a : ℕ → ℕ) (z : (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)) :
  Model.s1 (o,a,z) = a := rfl
@[simp] theorem Model.s2_pair (o a b : ℕ → ℕ) (z : ℕ × (ℕ → ℕ → Bool)) :
  Model.s2 (o,a,b,z) = b := rfl
@[simp] theorem Model.so_pair (o a b : ℕ → ℕ) (r : ℕ) (w : ℕ → ℕ → Bool) :
  Model.so (o,a,b,r,w) = r := rfl
@[simp] theorem Model.w_pair (o a b : ℕ → ℕ) (r : ℕ) (w : ℕ → ℕ → Bool) :
  Model.w (o,a,b,r,w) = w := rfl

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, M.op j < 3) ∧
  (∀ j < s, M.s1 j ≤ n + j) ∧
  (∀ j < s, M.s2 j ≤ n + j) ∧
  (M.so ≤ n + s) ∧
  (∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)) ∧
  (∀ r, R r → M.sv n s M.so r = g r)
abbrev Valid.op_lt {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.op j < 3 := h.1
abbrev Valid.s1_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.s1 j ≤ n + j := h.2.1
abbrev Valid.s2_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, M.s2 j ≤ n + j := h.2.2.1
abbrev Valid.so_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    M.so ≤ n + s := h.2.2.2.1
abbrev Valid.w_eq {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r) := h.2.2.2.2.1
abbrev Valid.out_eq {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (h : Valid n s g R M) :
    ∀ r, R r → M.sv n s M.so r = g r := h.2.2.2.2.2


end PEqualNP.Outside.L_meta_6349.LRAT.Link

namespace PEqualNP.Outside.L_meta_6349.LRAT.Link

lemma gfun_imp (op : Nat) (a b c d : Bool)
    (ha : a = true → c = true) (hb : b = true → d = true) :
    gfun op a b = true → gfun op c d = true := by
  unfold gfun
  split_ifs <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma unread_output_imp {n s : Nat} {g : Nat → Bool} {R : Nat → Prop} {M : Model}
    (hv : Valid n s g R M) {v r t : Nat} (hr : R r) (ht : R t)
    (hno : ∀ j < s, M.s1 j ≠ v ∧ M.s2 j ≠ v) (hso : M.so ≠ v)
    (hrow : ∀ k < n, k ≠ v → r.testBit k = true → t.testBit k = true) :
    g r = true → g t = true := by
  have hw : ∀ j, j < s → M.w j r = true → M.w j t = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have hs (k : Nat) (hk : k ≠ v) :
          M.sv n j k r = true → M.sv n j k t = true := by
        unfold Model.sv
        split_ifs with hkn hkj
        · exact hrow k hkn hk
        · exact ih (k - n) (by omega) (by omega)
        · simp
      rw [hv.w_eq j hj r hr, hv.w_eq j hj t ht]
      exact gfun_imp _ _ _ _ _ (hs _ (hno j hj).1) (hs _ (hno j hj).2)
  have hout : M.sv n s M.so r = true → M.sv n s M.so t = true := by
    unfold Model.sv
    split_ifs with hkn hkj
    · exact hrow M.so hkn hso
    · exact hw (M.so - n) (by omega)
    · simp
  simpa only [hv.out_eq r hr, hv.out_eq t ht] using hout

lemma read_of_witness {n s : Nat} {g : Nat → Bool} {R : Nat → Prop} {M : Model}
    (hv : Valid n s g R M) {v r t : Nat} (hr : R r) (ht : R t)
    (hso : M.so ≠ v)
    (hrow : ∀ k < n, k ≠ v → r.testBit k = true → t.testBit k = true)
    (hpos : g r = true) (hneg : g t = false) :
    ∃ j < s, M.s1 j = v ∨ M.s2 j = v := by
  classical
  by_contra h
  have hno : ∀ j < s, M.s1 j ≠ v ∧ M.s2 j ≠ v := by
    intro j hj
    exact ⟨fun h1 => h ⟨j, hj, Or.inl h1⟩, fun h2 => h ⟨j, hj, Or.inr h2⟩⟩
  have htrue := unread_output_imp hv hr ht hno hso hrow hpos
  rw [hneg] at htrue
  cases htrue

lemma output_ne_of_witness {n s : Nat} {g : Nat → Bool} {R : Nat → Prop} {M : Model}
    (hv : Valid n s g R M) {v r : Nat} (hvlt : v < n) (hr : R r)
    (hne : g r ≠ r.testBit v) : M.so ≠ v := by
  intro h
  have hout := hv.out_eq r hr
  rw [h] at hout
  simp only [Model.sv, if_pos hvlt] at hout
  exact hne hout.symm


def primaryRows : List Nat := [17,33,65,129,18,34,66,130,20,36,68,132,24,40,72,136]

def primaryGoal (r : Nat) : Bool := [17,65,129,34,130,36,68,24].contains r

lemma primaryGoal_correct : ∀ u v : Fin 4,
    primaryGoal (2 ^ u.val + 2 ^ (4 + v.val)) =
      (5805 : Nat).testBit (4 * u.val + v.val) := by decide

def primaryPos (v : Fin 8) : Nat := [17,34,36,24,17,34,65,129].getD v.val 0

def primaryNeg (v : Fin 8) : Nat := [18,33,33,18,33,18,33,33].getD v.val 0

def primaryOut (v : Fin 8) : Nat := [33,17,17,17,65,17,17,17].getD v.val 0

lemma primary_witnesses : ∀ v : Fin 8,
    primaryPos v ∈ primaryRows ∧ primaryNeg v ∈ primaryRows ∧
    primaryOut v ∈ primaryRows ∧
    primaryGoal (primaryPos v) = true ∧ primaryGoal (primaryNeg v) = false ∧
    primaryGoal (primaryOut v) ≠ (primaryOut v).testBit v.val ∧
    (∀ k : Fin 8, k ≠ v → (primaryPos v).testBit k.val = true →
      (primaryNeg v).testBit k.val = true) := by decide

lemma primary_reads_all {s : Nat} {M : Model}
    (hv : Valid 8 s primaryGoal (· ∈ primaryRows) M) :
    ∀ v < 8, ∃ j < s, M.s1 j = v ∨ M.s2 j = v := by
  intro v hvlt
  let vf : Fin 8 := ⟨v, hvlt⟩
  obtain ⟨hp, hn, ho, hpos, hneg, hout, hcmp⟩ := primary_witnesses vf
  have hso : M.so ≠ v := output_ne_of_witness hv hvlt ho hout
  apply read_of_witness hv hp hn hso _ hpos hneg
  intro k hk hkv hbit
  exact hcmp ⟨k, hk⟩ (fun he => hkv (congrArg Fin.val he)) hbit

end PEqualNP.Outside.L_meta_6349.LRAT.Link
