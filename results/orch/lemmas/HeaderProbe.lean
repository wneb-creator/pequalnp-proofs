import FastBench

namespace PEqualNP.Outside.L_meta_1677_HeaderProbe
open PEqualNP.Outside.L_meta_1677

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem arity_11 : (seedContexts 11 1003 16).all (fun c => c.2.1==11) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem prelim_11 : (seedContexts 11 1003 16).all (prelim graph) = true := by decide +kernel

end PEqualNP.Outside.L_meta_1677_HeaderProbe
