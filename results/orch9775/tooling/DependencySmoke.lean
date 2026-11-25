import DependencyCollector
import RelabelSurplus

namespace CollectorFixture
def usedOne : Nat := 1
def unusedTwo : Nat := 2
theorem viaUsed : usedOne = 1 := rfl
theorem finalProof : usedOne = 1 := viaUsed
end CollectorFixture

collect_own_dependencies CollectorFixture.finalProof within CollectorFixture
collect_own_dependencies PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools.relabel_Bplus within PEqualNP.Outside.L_meta_9775
