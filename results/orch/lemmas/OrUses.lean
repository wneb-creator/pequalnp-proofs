import OrTight

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

noncomputable def countHit {R} (P : Wire R → Prop) (a b : Wire R) : Nat := by
  classical exact if P a ∨ P b then 1 else 0

inductive CountRun {R} (u : Bool) (goal : Wire R) (P : Wire R → Prop) :
    Nat → Nat → List (Wire R) → Prop
  | stop : CountRun u goal P 0 0 [goal]
  | perm {s n xs zs} (h : CountRun u goal P s n xs) (p : xs.Perm zs) :
      CountRun u goal P s n zs
  | two {s n a b rest} (d : Nat) (hd : allowed u d) (ka kb : Bool)
      (h : CountRun u goal P s n (comb d a b :: kept ka a (kept kb b rest))) :
      CountRun u goal P (s + 1) (n + countHit P a b) (a :: b :: rest)

lemma Run.counted {R u} {goal : Wire R} {s ws} (h : Run u goal s ws)
    (P : Wire R → Prop) : ∃ n, CountRun u goal P s n ws := by
  induction h using Run.ind with
  | stop => exact ⟨0, CountRun.stop⟩
  | perm p h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n, CountRun.perm hn p⟩
  | two d hd ka kb h ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + countHit P _ _, CountRun.two d hd ka kb hn⟩

lemma reach_comb_paid {R u} {roots bank : List (Wire R)} {p d a b}
    (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ next, Reach u roots (p + 1) next ∧ Available u next (comb d a b) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨op, x, y, he, hx, hy, _, _⟩ := comb_prime hd ha hb
  refine ⟨combine op x y :: bank, Reach.two op hp hx hy, ?_, ?_⟩
  · rw [he]
    exact Or.inl (by simp)
  · exact fun v hv => available_cons _ hv

lemma counted_projection {R S u} (rows : S → R) {goal : Wire R}
    {P : Wire R → Prop} {s n ws} (h : CountRun u goal P s n ws)
    (hc : ∀ a, P a → Constant (restrictRows rows a))
    {roots : List (Wire S)} {p bank}
    (hp : Reach u roots p bank)
    (hs : supply u bank (ws.map (restrictRows rows))) :
    ∃ q next, Reach u roots q next ∧ Available u next (restrictRows rows goal) ∧
      q + n ≤ p + s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p, bank, hp, hs _ (by simp), by omega⟩
  | perm h perm ih =>
    exact ih hp (fun v hv => hs v ((perm.map _).mem_iff.mp hv))
  | @two s n a b rest d hd ka kb h ih =>
    have ha := hs (restrictRows rows a) (by simp)
    have hb := hs (restrictRows rows b) (by simp)
    have tailSupply {next : List (Wire S)}
        (hg : Available u next (comb d (restrictRows rows a) (restrictRows rows b)))
        (inc : ∀ v, Available u bank v → Available u next v) :
        supply u next
          ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
      simp only [List.map_cons, restrict_kept, restrict_comb]
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hg
      · apply inc v
        rcases mem_kept hv with rfl | hv
        · exact ha
        · rcases mem_kept hv with rfl | hv
          · exact hb
          · exact hs v (by simp [hv])
    by_cases hit : P a ∨ P b
    · have hg := from_constant_comb hd (hit.imp (hc a) (hc b)) ha hb
      obtain ⟨q, next, hq, hv, hbound⟩ := ih hp (tailSupply hg (fun _ h => h))
      refine ⟨q, next, hq, hv, ?_⟩
      simp only [countHit, ite_eq_left hit]
      omega
    · obtain ⟨next, hn, hg, inc⟩ := reach_comb_paid hd hp ha hb
      obtain ⟨q, final, hq, hv, hbound⟩ := ih hn (tailSupply hg inc)
      refine ⟨q, final, hq, hv, ?_⟩
      simp only [countHit, ite_eq_right hit]
      omega

lemma counted_projection_lower {R S u} (rows : S → R) {goal : Wire R}
    {P : Wire R → Prop} {s n ws} (h : CountRun u goal P s n ws)
    (hc : ∀ a, P a → Constant (restrictRows rows a))
    {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank)
    (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + n ≤ p + s := by
  obtain ⟨q, next, hq, hg, hbound⟩ := counted_projection rows h hc hp hs
  have hlow := hl q next hq hg
  omega

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
