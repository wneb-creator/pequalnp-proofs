import SuccessorChecker

namespace PEqualNP.Outside.L_meta_2373.Live1024

def cofactorCheck (u : Bool) (raw : List Sig) (d : Sig) (L cap : Nat)
    (ws : List Sig) (cs : List Choice) : Bool :=
  decide ws.Nodup && match makePool u d raw cs with
    | none => false
    | some pool => poolCut u d L cap cs.length pool ws

lemma cofactorCheck_sound {u raw T d L cap ws cs} (slice : Slice u raw T d L)
    (check : cofactorCheck u raw d L cap ws cs = true) :
    Impossible u T cap ws.toFinset := by
  have both := Bool.and_eq_true_iff.mp check
  have nd : ws.Nodup := of_decide_eq_true both.1
  cases built : makePool u d raw cs with
  | none => simp [built] at both
  | some pool =>
    have cut : poolCut u d L cap cs.length pool ws = true := by simpa [built] using both.2
    exact poolCut_sound slice cs built nd cut

end PEqualNP.Outside.L_meta_2373.Live1024
