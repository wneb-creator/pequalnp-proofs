import FastBench

namespace PEqualNP.Outside.L_meta_1677_EightProbe
open PEqualNP.Outside.L_meta_1677 PEqualNP.Outside.L_meta_1677_FastBench

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem body_11_1003 : probe_runBatch true 11 11 (seedContexts 11 1003 8) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem body_11_1011 : probe_runBatch true 11 11 (seedContexts 11 1011 8) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem body_12_901 : probe_runBatch true 12 12 (seedContexts 12 901 8) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem body_12_909 : probe_runBatch true 12 12 (seedContexts 12 909 8) = true := by decide +kernel

end PEqualNP.Outside.L_meta_1677_EightProbe
