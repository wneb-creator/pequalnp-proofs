import NonOrSeed

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

abbrev TraceGate := Nat × (Sig × Sig)

def traceValue (g : TraceGate) : Sig := bin g.1 g.2.1 g.2.2

def traceBank (w : List Sig) (gs : List TraceGate) : List Sig :=
  gs.foldl (fun w g => w ++ [traceValue g]) w

def TraceValid (u : Bool) : List Sig → List TraceGate → Prop
  | _,[] => True
  | w,g::gs => allowed u g.1 ∧ proper g.2.1 ∧ proper g.2.2 ∧ g.2.1 ≠ g.2.2 ∧
      g.2.1 ∈ w ∧ g.2.2 ∈ w ∧ TraceValid u (w ++ [traceValue g]) gs

lemma traceBank_eq (w : List Sig) (gs : List TraceGate) :
    traceBank w gs = w ++ gs.map traceValue := by
  induction gs generalizing w with
  | nil => simp [traceBank]
  | cons g gs ih =>
    change traceBank (w ++ [traceValue g]) gs = _
    rw [ih]
    simp [List.append_assoc]

lemma traceValid_mono {u w gs} (valid : TraceValid u w gs) (v : List Sig)
    (sub : ∀ a ∈ w, a ∈ v) : TraceValid u v gs := by
  induction gs generalizing w v with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hd,ha,hb,hab,hmA,hmB,tail⟩ := valid
    refine ⟨hd,ha,hb,hab,sub _ hmA,sub _ hmB,ih tail _ ?_⟩
    intro a h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_append.mpr (Or.inl (sub a h))
    · exact List.mem_append.mpr (Or.inr h)

lemma live_trace {u T k S} (run : Live u T k S) (w : List Sig)
    (supply : ∀ a ∈ S, a ∈ w) :
    ∃ gs : List TraceGate, gs.length = k ∧ TraceValid u w gs ∧ T ∈ traceBank w gs := by
  induction run using Live.ind generalizing w with
  | stop hp =>
    exact ⟨[],rfl,True.intro,supply T (by simp)⟩
  | @binary k U a b d hd ha hb hab fresh tail ih =>
    let g : TraceGate := (d,a,b)
    have hs : ∀ z ∈ insert (bin d a b) U, z ∈ w ++ [traceValue g] := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact List.mem_append.mpr (Or.inr (by simp [g,traceValue]))
      · exact List.mem_append.mpr (Or.inl (supply z (by simp [hz])))
    obtain ⟨gs,hlen,hv,hout⟩ := ih (w ++ [traceValue g]) hs
    exact ⟨g::gs,by simp [hlen],⟨hd,ha,hb,hab,supply a (by simp),supply b (by simp),hv⟩,hout⟩

def skippedCost (q : Sig) (gs : List TraceGate) : Nat :=
  gs.countP (fun g => decide (traceValue g ≠ q))

lemma extract_trace_skip {u T} (q : Sig) (gs : List TraceGate) (w : List Sig)
    (valid : TraceValid u w gs) (hq : q ∈ w) (hp : proper T)
    (hout : T ∈ traceBank w gs) :
    ∃ k S, k ≤ skippedCost q gs ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0,{T},by simp [skippedCost],Live.stop hp,by simpa [traceBank] using hout⟩
  | cons g gs ih =>
    obtain ⟨hd,ha,hb,hab,hmA,hmB,tail⟩ := valid
    obtain ⟨k,S,hk,run,hs⟩ := ih (w ++ [traceValue g]) tail
      (List.mem_append.mpr (Or.inl hq)) hout
    let c := if traceValue g = q then 0 else 1
    have step : represented w (traceValue g) ∨ (c=1 ∧ witness u w (traceValue g)) := by
      by_cases h : traceValue g = q
      · exact Or.inl (Or.inl (h.symm ▸ hq))
      · exact Or.inr ⟨by simp [c,h],g.1,g.2.1,g.2.2,hd,hmA,hmB,ha,hb,hab,rfl⟩
    obtain ⟨l,R,hl,hr,hsupply⟩ := pull_gate run step hs
    refine ⟨l,R,?_,hr,hsupply⟩
    by_cases h : traceValue g = q <;> simp [skippedCost,h,c] at hk hl ⊢ <;> omega

lemma skippedCost_lt {q : Sig} {gs : List TraceGate}
    (occurs : q ∈ gs.map traceValue) : skippedCost q gs < gs.length := by
  induction gs with
  | nil => simp at occurs
  | cons g gs ih =>
    have bound := List.countP_le_length (p := fun a => decide (traceValue a ≠ q)) (l := gs)
    by_cases h : traceValue g = q
    · simp [skippedCost,h]
      exact bound
    · have htail : q ∈ gs.map traceValue := by
        simp only [List.map_cons,List.mem_cons] at occurs
        exact occurs.resolve_left (Ne.symm h)
      have hsmall := ih htail
      simpa [skippedCost,List.countP_cons,h] using hsmall

lemma supply_trace_result {u T} (q : Sig) (gs : List TraceGate) (w : List Sig)
    (valid : TraceValid u w gs) (hp : proper T) (hout : T ∈ traceBank w gs)
    (occurs : q ∈ gs.map traceValue) :
    ∃ k S, k < gs.length ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ w ++ [q] := by
  have vplus := traceValid_mono valid (w ++ [q]) (fun a ha => List.mem_append.mpr (Or.inl ha))
  have outplus : T ∈ traceBank (w ++ [q]) gs := by
    rw [traceBank_eq] at hout ⊢
    rcases List.mem_append.mp hout with h | h
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))
    · exact List.mem_append.mpr (Or.inr h)
  obtain ⟨k,S,hk,run,supply⟩ := extract_trace_skip q gs (w ++ [q]) vplus (by simp) hp outplus
  exact ⟨k,S,lt_of_le_of_lt hk (skippedCost_lt occurs),run,supply⟩

lemma nonOr_trace_floor (gs : List TraceGate) (valid : TraceValid true pins gs)
    (hout : target ∈ traceBank pins gs) (d : Nat) (a b : Sig)
    (allowed : allowed true d) (nonOr : d ≠ 1)
    (ha : a ∈ pins) (hb : b ∈ pins) (hab : a ≠ b)
    (occurs : bin d a b ∈ gs.map traceValue) : 18 ≤ gs.length := by
  have hp : proper target := by unfold proper;decide +kernel
  obtain ⟨k,S,hk,run,supply⟩ := supply_trace_result (bin d a b) gs pins valid hp hout occurs
  have floor := pair_seventeen allowed nonOr ha hb hab run (fun v hv => by simpa using supply v hv)
  omega

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
