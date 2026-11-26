import PackedH1_0768_0799
import PackedH1_0800_0831
import PackedH1_0832_0863
import PackedH1_0864_0895
import PackedH1_0896_0927
import PackedH1_0928_0959
import PackedH1_0960_0991
import PackedH1_0992_1023
import PackedH1_1024_1055
import PackedH1_1056_1087
import PackedH1_1088_1119
import PackedH1_1120_1151
import PackedH1_1152_1183
import PackedH1_1184_1215
import PackedH1_1216_1247
import PackedH1_1248_1279
import PackedH1_1280_1311
import PackedH1_1312_1343
import PackedH1_1344_1375
import PackedH1_1376_1407
import PackedH1_1408_1439
import PackedH1_1440_1471
import PackedH1_1472_1503
import PackedH1_1504_1535

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks.Aggregate
open Replay.DirectMode.Packed
set_option maxHeartbeats 0
lemma checked (i : Fin 5230) (lo : 768 ≤ i.val) (hi : i.val < 1536) :
    checkNode i = true := by
  by_cases upper_800 : i.val < 800
  · exact checked_0768_0799 i lo upper_800
  have lower_800 : 800 ≤ i.val := by omega
  by_cases upper_832 : i.val < 832
  · exact checked_0800_0831 i lower_800 upper_832
  have lower_832 : 832 ≤ i.val := by omega
  by_cases upper_864 : i.val < 864
  · exact checked_0832_0863 i lower_832 upper_864
  have lower_864 : 864 ≤ i.val := by omega
  by_cases upper_896 : i.val < 896
  · exact checked_0864_0895 i lower_864 upper_896
  have lower_896 : 896 ≤ i.val := by omega
  by_cases upper_928 : i.val < 928
  · exact checked_0896_0927 i lower_896 upper_928
  have lower_928 : 928 ≤ i.val := by omega
  by_cases upper_960 : i.val < 960
  · exact checked_0928_0959 i lower_928 upper_960
  have lower_960 : 960 ≤ i.val := by omega
  by_cases upper_992 : i.val < 992
  · exact checked_0960_0991 i lower_960 upper_992
  have lower_992 : 992 ≤ i.val := by omega
  by_cases upper_1024 : i.val < 1024
  · exact checked_0992_1023 i lower_992 upper_1024
  have lower_1024 : 1024 ≤ i.val := by omega
  by_cases upper_1056 : i.val < 1056
  · exact checked_1024_1055 i lower_1024 upper_1056
  have lower_1056 : 1056 ≤ i.val := by omega
  by_cases upper_1088 : i.val < 1088
  · exact checked_1056_1087 i lower_1056 upper_1088
  have lower_1088 : 1088 ≤ i.val := by omega
  by_cases upper_1120 : i.val < 1120
  · exact checked_1088_1119 i lower_1088 upper_1120
  have lower_1120 : 1120 ≤ i.val := by omega
  by_cases upper_1152 : i.val < 1152
  · exact checked_1120_1151 i lower_1120 upper_1152
  have lower_1152 : 1152 ≤ i.val := by omega
  by_cases upper_1184 : i.val < 1184
  · exact checked_1152_1183 i lower_1152 upper_1184
  have lower_1184 : 1184 ≤ i.val := by omega
  by_cases upper_1216 : i.val < 1216
  · exact checked_1184_1215 i lower_1184 upper_1216
  have lower_1216 : 1216 ≤ i.val := by omega
  by_cases upper_1248 : i.val < 1248
  · exact checked_1216_1247 i lower_1216 upper_1248
  have lower_1248 : 1248 ≤ i.val := by omega
  by_cases upper_1280 : i.val < 1280
  · exact checked_1248_1279 i lower_1248 upper_1280
  have lower_1280 : 1280 ≤ i.val := by omega
  by_cases upper_1312 : i.val < 1312
  · exact checked_1280_1311 i lower_1280 upper_1312
  have lower_1312 : 1312 ≤ i.val := by omega
  by_cases upper_1344 : i.val < 1344
  · exact checked_1312_1343 i lower_1312 upper_1344
  have lower_1344 : 1344 ≤ i.val := by omega
  by_cases upper_1376 : i.val < 1376
  · exact checked_1344_1375 i lower_1344 upper_1376
  have lower_1376 : 1376 ≤ i.val := by omega
  by_cases upper_1408 : i.val < 1408
  · exact checked_1376_1407 i lower_1376 upper_1408
  have lower_1408 : 1408 ≤ i.val := by omega
  by_cases upper_1440 : i.val < 1440
  · exact checked_1408_1439 i lower_1408 upper_1440
  have lower_1440 : 1440 ≤ i.val := by omega
  by_cases upper_1472 : i.val < 1472
  · exact checked_1440_1471 i lower_1440 upper_1472
  have lower_1472 : 1472 ≤ i.val := by omega
  by_cases upper_1504 : i.val < 1504
  · exact checked_1472_1503 i lower_1472 upper_1504
  have lower_1504 : 1504 ≤ i.val := by omega
  exact checked_1504_1535 i lower_1504 hi
#check checked
#print axioms checked
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks.Aggregate
