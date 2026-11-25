import UpstreamGraph

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def weightSpecs : List WeightSpec := [
(5,256,5,1,0,0x0,0x24480000000000000000000000000000),
(6,8192,6,1,0,0x0,0x6c0000000000000000000000000000000000000000000000),
(17,1024,17,1,0,0x0,0x92200000000000000000000000000000000000),
(18,8192,18,1,0,0x0,0x1830000000000000000000000000000000000000000000000),
(20,8192,20,1,0,0x0,0x1428000000000000000000000000000000000000000000000),
(24,2048,24,1,0,0x0,0x511800000000000000000000000000000000000000),
(33,1024,33,1,0,0x0,0x31800000000000000000000000000000000000),
(34,512,34,1,0,0x0,0x43540000000000000000000000000000000),
(48,1024,48,1,0,0x0,0x180700000000000000000000000000000000000),
(65,256,65,1,0,0x0,0x60c0000000000000000000000000000),
(66,512,66,1,0,0x0,0x6c00000000000000000000000000000000),
(68,256,68,1,0,0x0,0x22090000000000000000000000000000),
(72,2048,72,1,0,0x0,0x6c000000000000000000000000000000000000000),
(80,2048,80,1,0,0x0,0x142800000000000000000000000000000000000000),
(96,512,96,1,0,0x0,0x14280000000000000000000000000000000),
(640,2,640,1,0,0x0,0x81a4000),
(768,64,768,1,0,0x0,0x827000000000000000000000),
(1536,32,1536,1,0,0x0,0x415c00000000000000000),
(2176,8,2176,1,0,0x0,0x415c0000000000),
(2304,64,2304,1,0,0x0,0x21d000000000000000000000),
(2560,64,2560,1,0,0x0,0x13a000000000000000000000),
(3072,16,3072,1,0,0x0,0x206900000000000000),
(4224,8,4224,1,0,0x0,0x209c0000000000),
(4608,32,4608,1,0,0x0,0x113800000000000000000),
(5120,32,5120,1,0,0x0,0x87400000000000000000),
(6144,8,6144,1,0,0x0,0x3d40000000000),
(8320,2,8320,1,0,0x0,0x874000),
(8704,2,8704,1,0,0x0,0x3d4000),
(9216,16,9216,1,0,0x0,0x82700000000000000),
(10240,16,10240,1,0,0x0,0x44e00000000000000),
(7,8448,7,2,1,0xd802,0x6c0000000000000024480000000000000000000000000000),
(19,9216,19,2,1,0xda04,0x1830000000212800000000000000000000000000000000000),
(21,1280,21,2,1,0xa800,0x92200024480000000000000000000000000000),
(25,3072,25,2,1,0xba04,0x511892200000000000000000000000000000000000),
(26,10240,26,2,1,0xdb04,0x2294000838400000000000000000000000000000000000000),
(28,10240,28,2,1,0xdb04,0x2488000838400000000000000000000000000000000000000),
(35,1536,35,2,1,0xa905,0x31853100000000000000000000000000000000),
(37,1280,37,2,1,0xa800,0x31800024480000000000000000000000000000),
(38,8704,38,2,1,0xd901,0xc60000000000091200000000000000000000000000000000),
(50,1536,50,2,1,0xa905,0x1a8553100000000000000000000000000000000),
(52,9216,52,2,1,0xda04,0x1428000000220900000000000000000000000000000000000),
(56,3072,56,2,1,0xba04,0x511980700000000000000000000000000000000000),
(67,768,67,2,1,0x9806,0x6c060c0000000000000000000000000000),
(70,768,70,2,1,0x9806,0x6c22090000000000000000000000000000),
(73,2304,73,2,1,0xb806,0x6c00000001c060000000000000000000000000000),
(74,2560,74,2,1,0xb906,0x4a5400022940000000000000000000000000000000),
(76,2304,76,2,1,0xb806,0x6c000000028a10000000000000000000000000000),
(81,1280,81,2,1,0xa800,0x922000060c0000000000000000000000000000),
(82,2560,82,2,1,0xb906,0x183000022940000000000000000000000000000000),
(84,2304,84,2,1,0xb806,0x142800000028a10000000000000000000000000000),
(97,768,97,2,1,0x9806,0x142860c0000000000000000000000000000),
(100,768,100,2,1,0x9806,0x142a2090000000000000000000000000000),
(104,2560,104,2,1,0xb906,0x4a54000601c0000000000000000000000000000000),
(112,1536,112,2,1,0xa905,0x1a8514280000000000000000000000000000000),
(896,66,896,2,1,0x6109,0x8270000000000000081a4000),
(1664,34,1664,2,1,0x5109,0x415c000000000081a4000),
(1792,96,1792,2,1,0x6509,0x827415c00000000000000000),
(2432,72,2432,2,1,0x630b,0x21d0000000415c0000000000),
(2688,10,2688,2,1,0x3107,0x415c00081a4000),
(3200,24,3200,2,1,0x430b,0x2069415c0000000000),
(3328,80,3328,2,1,0x640b,0x21d000206900000000000000),
(3584,48,3584,2,1,0x540a,0x415e06900000000000000),
(4736,10,4736,2,1,0x3107,0x209c00081a4000),
(4864,96,4864,2,1,0x6509,0x827113800000000000000000),
(5248,40,5248,2,1,0x530c,0x874000209c0000000000),
(6400,72,6400,2,1,0x630b,0x21d000000003d40000000000),
(6656,40,6656,2,1,0x530c,0x113800003d40000000000),
(7168,24,7168,2,1,0x430b,0x206903d40000000000),
(8960,66,8960,2,1,0x6109,0x8270000000000000003d4000),
(9344,18,9344,2,1,0x410d,0x82700000000874000),
(9728,18,9728,2,1,0x410d,0x827000000003d4000),
(10368,10,10368,2,1,0x3107,0x415c0000874000),
(10496,80,10496,2,1,0x640b,0x21d000044e00000000000000),
(10752,18,10752,2,1,0x410d,0x44e000000003d4000),
(12416,10,12416,2,1,0x3107,0x209c0000874000),
(12800,34,12800,2,1,0x5109,0x1138000000000003d4000),
(13312,48,13312,2,1,0x540a,0x87482700000000000000),
(14336,24,14336,2,1,0x430b,0x44e03d40000000000),
(27,11264,27,3,2,0xdba44,0x7a10000d3029a000000000000000000000000000000000000),
(29,11264,29,3,2,0xdba44,0x7408000d3029a000000000000000000000000000000000000),
(58,11264,58,3,2,0xdba44,0x7a10000d303a8100000000000000000000000000000000000),
(60,11264,60,3,2,0xdba44,0x7408000d303a8100000000000000000000000000000000000),
(75,2816,75,3,2,0xb9866,0x4e40000a681e840000000000000000000000000000),
(78,2816,78,3,2,0xb9866,0x4e40000a683a810000000000000000000000000000),
(83,2816,83,3,2,0xb9866,0x9c20000a681e840000000000000000000000000000),
(85,11264,85,3,2,0xdba44,0x74080009c229a000000000000000000000000000000000000),
(86,2816,86,3,2,0xb9866,0x9c20000a683a810000000000000000000000000000),
(105,2816,105,3,2,0xb9866,0x4e400007409e840000000000000000000000000000),
(108,2816,108,3,2,0xb9866,0x4e40000740ba810000000000000000000000000000),
(113,2816,113,3,2,0xb9866,0x9c200007409e840000000000000000000000000000),
(114,11264,114,3,2,0xdba44,0x7a100009c23a8100000000000000000000000000000000000),
(116,2816,116,3,2,0xb9866,0x9c20000740ba810000000000000000000000000000),
(657,1026,657,2,0,0x0,0x92200000000000000000000000000009120000),
(660,8194,660,2,0,0x0,0x14280000000000000000000000000000000000000081a4000),
(792,2112,792,2,0,0x0,0x511800000000000000827000000000000000000000),
(1920,98,1920,3,2,0x65199,0x827415c000000000081a4000),
(2181,264,2181,2,0,0x0,0x24480000000000000044480000000000),
(2209,1032,2209,2,0,0x0,0x31800000000000000000000051180000000000),
(2338,576,2338,2,0,0x0,0x4354000000021d000000000000000000000),
(2565,320,2565,2,0,0x0,0x2448000013a000000000000000000000),
(3078,8208,3078,2,0,0x0,0x6c0000000000000000000000000000206900000000000000),
(3456,88,3456,3,2,0x643bb,0x21d0002069415c0000000000),
(3712,98,3712,3,2,0x65199,0x13a415c000000000081a4000),
(4229,264,4229,2,0,0x0,0x24480000000000000024880000000000),
(4289,264,4289,2,0,0x0,0x60c0000000000000024880000000000),
(4292,264,4292,2,0,0x0,0x22090000000000000024880000000000),
(4304,2056,4304,2,0,0x0,0x1428000000000000000000000000209c0000000000),
(4625,1056,4625,2,0,0x0,0x92200000000000000113800000000000000000),
(4628,8224,4628,2,0,0x0,0x2488000000000000000000000000912000000000000000000),
(4992,98,4992,3,2,0x65199,0x8271138000000000081a4000),
(5126,8224,5126,2,0,0x0,0x6c0000000000000000000000000882400000000000000000),
(5186,544,5186,2,0,0x0,0x6c00000000000087400000000000000000),
(5188,288,5188,2,0,0x0,0x28a100000000c6000000000000000000),
(6149,264,6149,2,0,0x0,0x24480000000000000006c00000000000),
(6150,8200,6150,2,0,0x0,0xc60000000000000000000000000000000083840000000000),
(6784,98,6784,3,2,0x65199,0x13a1138000000000081a4000),
(7424,88,7424,3,2,0x643bb,0x21d000206903d40000000000),
(7680,88,7680,3,2,0x643bb,0x13a000206903d40000000000),
(8353,1026,8353,2,0,0x0,0x111200000000000000000000000000001830000),
(8385,258,8385,2,0,0x0,0x1c060000000000000000000000c60000),
(8416,514,8416,2,0,0x0,0x14280000000000000000000000000874000),
(9288,2064,9288,2,0,0x0,0x6c000000000000000000000082700000000000000),
(9984,98,9984,3,2,0x65199,0x827415c000000000003d4000),
(10273,1040,10273,2,0,0x0,0x31800000000000000000044e00000000000000),
(10624,88,10624,3,2,0x643bb,0x21d000044e415c0000000000),
(10880,88,10880,3,2,0x643bb,0x13a000044e415c0000000000),
(11776,98,11776,3,2,0x65199,0x13a415c000000000003d4000),
(13056,98,13056,3,2,0x65199,0x8271138000000000003d4000),
(14592,88,14592,3,2,0x643bb,0x21d000044e03d40000000000),
(14848,98,14848,3,2,0x65199,0x13a1138000000000003d4000)]

def weights : List (Nat × Nat) := [(5,1),(6,1),(17,1),(18,1),(20,1),(24,1),(33,1),(34,1),(48,1),(65,1),(66,1),(68,1),(72,1),(80,1),(96,1),(640,1),(768,1),(1536,1),(2176,1),(2304,1),(2560,1),(3072,1),(4224,1),(4608,1),(5120,1),(6144,1),(8320,1),(8704,1),(9216,1),(10240,1),(7,2),(19,2),(21,2),(25,2),(26,2),(28,2),(35,2),(37,2),(38,2),(50,2),(52,2),(56,2),(67,2),(70,2),(73,2),(74,2),(76,2),(81,2),(82,2),(84,2),(97,2),(100,2),(104,2),(112,2),(896,2),(1664,2),(1792,2),(2432,2),(2688,2),(3200,2),(3328,2),(3584,2),(4736,2),(4864,2),(5248,2),(6400,2),(6656,2),(7168,2),(8960,2),(9344,2),(9728,2),(10368,2),(10496,2),(10752,2),(12416,2),(12800,2),(13312,2),(14336,2),(27,3),(29,3),(58,3),(60,3),(75,3),(78,3),(83,3),(85,3),(86,3),(105,3),(108,3),(113,3),(114,3),(116,3),(657,2),(660,2),(792,2),(1920,3),(2181,2),(2209,2),(2338,2),(2565,2),(3078,2),(3456,3),(3712,3),(4229,2),(4289,2),(4292,2),(4304,2),(4625,2),(4628,2),(4992,3),(5126,2),(5186,2),(5188,2),(6149,2),(6150,2),(6784,3),(7424,3),(7680,3),(8353,2),(8385,2),(8416,2),(9288,2),(9984,3),(10273,2),(10624,3),(10880,3),(11776,3),(13056,3),(14592,3),(14848,3)]
def clean (m : Nat) : Bool := edges.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def possible (cap m : Nat) : Bool :=
  clean m && (let c := (mask m).card
              decide (14 ≤ c+cap) && weights.all (fun r =>
                (r.1 &&& m != r.1) || decide (14+r.2 ≤ c+cap)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem repr (I : Finset V) : ∃ m : Fin 16384, mask m.val = I := by
  let bs := List.ofFn (fun i : V => decide (i∈I))
  let B := BitVec.ofBoolListLE bs
  have hl : bs.length=14 := List.length_ofFn
  have lt : B.toNat < 16384 := by have h := B.isLt; change _ < 2 ^ bs.length at h; simpa [hl] using h
  refine ⟨⟨B.toNat,lt⟩,?_⟩
  ext i
  simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and]
  change B.getLsbD i.val = true ↔ i∈I
  rw [BitVec.getLsbD_ofBoolListLE]
  have g := input_bit (fun i : V => decide (i∈I)) i
  simp only [bs,g,decide_eq_true_eq]

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem mask_sub (k m : Nat) (e : k &&& m = k) : mask k ⊆ mask m := by
  intro v hv
  simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and] at *
  have h := congrArg (fun z : Nat => z.testBit v.val) e
  change (k &&& m).testBit v.val = k.testBit v.val at h
  simpa only [Nat.testBit_and,hv,Bool.true_and] using h

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem weightRows : weightSpecs.all weightValid=true := by decide +kernel

theorem weightNames : weightSpecs.map weightKey=weights := by decide +kernel

theorem checked_weights {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) :
    ∀ r∈weights, mask r.1 ⊆ ineligSet 14 D → (eligSet 14 D).card+r.2 ≤ Bplus 14 D := by
  intro r hr sub
  rw [←weightNames] at hr
  obtain ⟨w,mem,rfl⟩ := List.mem_map.mp hr
  exact compact_weight h hc w (List.all_eq_true.mp weightRows _ mem) sub

theorem possible_of {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (cap m : Nat) (enc : mask m = ineligSet 14 D) (lim : Bplus 14 D ≤ cap) : possible cap m = true := by
  have p := inelig_card_add 14 D
  rw [←enc] at p
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have pc := elig_le_Bplus h.1 b hb
  have cleanM : clean m = true := by
    rw [clean,List.all_eq_true]
    rintro ⟨u,v⟩ e
    have bounds : ∀ q ∈ edges, q.1<14 ∧ q.2<14 := by decide +kernel
    obtain ⟨hu,hv⟩ := bounds (u,v) e
    have a := sem_elig_cover graph_ok h hc ((graph_edges ⟨u,hu⟩ ⟨v,hv⟩).2 (Or.inl e))
    by_contra! fail
    have both : m.testBit u=true ∧ m.testBit v=true := by simpa using fail
    have add (x : V) (hx : m.testBit x.val=true) : x ∉ eligSet 14 D := by
      apply sem_mem_inelig.mp
      rw [←enc]; simpa [mask] using hx
    exact a.elim (add _ both.1) (add _ both.2)
  simp only [possible,cleanM,Bool.true_and,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨by omega,?_⟩
  intro r hr
  by_cases eq : r.1 &&& m = r.1
  · have sub : mask r.1 ⊆ ineligSet 14 D := enc ▸ mask_sub _ _ eq
    have w := checked_weights h hc r hr sub
    have enough : 14+r.2 ≤ (mask m).card+cap := by omega
    simp [eq,enough]
  · simp [eq]

def tenMasks : List Nat := [127, 1290, 4757, 8488, 16256]

def elevenMasks : List Nat := [11, 44, 47, 55, 63, 95, 103, 111, 119, 123, 125, 126, 127, 164, 177, 181, 197, 229, 245, 266, 296, 298, 400, 416, 432, 521, 524, 525, 645, 661, 1034, 1036, 1038, 1156, 1216, 1220, 1282, 1288, 1290, 1408, 1548, 2051, 2084, 2087, 2212, 2213, 2693, 4099, 4118, 4119, 4165, 4167, 4183, 4241, 4244, 4245, 4293, 4305, 4308, 4309, 4354, 4368, 4370, 4496, 4613, 4629, 4741, 4753, 4756, 4757, 5190, 5316, 5378, 5636, 5764, 6147, 6151, 6273, 6276, 6277, 6661, 6789, 7174, 7300, 7812, 8064, 8201, 8232, 8233, 8417, 8456, 8480, 8488, 8608, 8713, 8833, 9480, 10401, 12160, 12289, 12352, 12353, 12481, 12544, 12929, 13504, 13696, 13952, 14208, 14465, 14977, 15232, 15488, 15744, 16000, 16128, 16256]

def classTest (m : Nat) : Bool :=
  !possible 9 m && (!possible 10 m || tenMasks.contains m) &&
    (!possible 11 m || elevenMasks.contains m)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk0 : ∀ j : Fin 1024, classTest (0+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk1 : ∀ j : Fin 1024, classTest (1024+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk2 : ∀ j : Fin 1024, classTest (2048+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk3 : ∀ j : Fin 1024, classTest (3072+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk4 : ∀ j : Fin 1024, classTest (4096+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk5 : ∀ j : Fin 1024, classTest (5120+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk6 : ∀ j : Fin 1024, classTest (6144+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk7 : ∀ j : Fin 1024, classTest (7168+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk8 : ∀ j : Fin 1024, classTest (8192+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk9 : ∀ j : Fin 1024, classTest (9216+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk10 : ∀ j : Fin 1024, classTest (10240+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk11 : ∀ j : Fin 1024, classTest (11264+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk12 : ∀ j : Fin 1024, classTest (12288+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk13 : ∀ j : Fin 1024, classTest (13312+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk14 : ∀ j : Fin 1024, classTest (14336+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem classChunk15 : ∀ j : Fin 1024, classTest (15360+j.val)=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem all_classes (m : Fin 16384) : classTest m.val=true := by
  let j : Fin 1024 := ⟨m.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hj : j.val=m.val % 1024 := rfl
  by_cases q0 : m.val/1024=0
  · have eq : m.val=0+j.val := by omega
    rw [eq]; exact classChunk0 j
  by_cases q1 : m.val/1024=1
  · have eq : m.val=1024+j.val := by omega
    rw [eq]; exact classChunk1 j
  by_cases q2 : m.val/1024=2
  · have eq : m.val=2048+j.val := by omega
    rw [eq]; exact classChunk2 j
  by_cases q3 : m.val/1024=3
  · have eq : m.val=3072+j.val := by omega
    rw [eq]; exact classChunk3 j
  by_cases q4 : m.val/1024=4
  · have eq : m.val=4096+j.val := by omega
    rw [eq]; exact classChunk4 j
  by_cases q5 : m.val/1024=5
  · have eq : m.val=5120+j.val := by omega
    rw [eq]; exact classChunk5 j
  by_cases q6 : m.val/1024=6
  · have eq : m.val=6144+j.val := by omega
    rw [eq]; exact classChunk6 j
  by_cases q7 : m.val/1024=7
  · have eq : m.val=7168+j.val := by omega
    rw [eq]; exact classChunk7 j
  by_cases q8 : m.val/1024=8
  · have eq : m.val=8192+j.val := by omega
    rw [eq]; exact classChunk8 j
  by_cases q9 : m.val/1024=9
  · have eq : m.val=9216+j.val := by omega
    rw [eq]; exact classChunk9 j
  by_cases q10 : m.val/1024=10
  · have eq : m.val=10240+j.val := by omega
    rw [eq]; exact classChunk10 j
  by_cases q11 : m.val/1024=11
  · have eq : m.val=11264+j.val := by omega
    rw [eq]; exact classChunk11 j
  by_cases q12 : m.val/1024=12
  · have eq : m.val=12288+j.val := by omega
    rw [eq]; exact classChunk12 j
  by_cases q13 : m.val/1024=13
  · have eq : m.val=13312+j.val := by omega
    rw [eq]; exact classChunk13 j
  by_cases q14 : m.val/1024=14
  · have eq : m.val=14336+j.val := by omega
    rw [eq]; exact classChunk14 j
  by_cases q15 : m.val/1024=15
  · have eq : m.val=15360+j.val := by omega
    rw [eq]; exact classChunk15 j
  omega

theorem surplus_ten {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : 10 ≤ Bplus 14 D := by
  obtain ⟨m, enc⟩ := repr (ineligSet 14 D)
  have cls := all_classes m
  simp only [classTest, Bool.and_eq_true] at cls
  by_contra hn
  have yes := possible_of h hc 9 m.val enc (by omega)
  simpa only [yes, Bool.not_true, Bool.false_eq_true] using cls.1.1

theorem length_twenty_three {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : 23 ≤ D.length := by
  have lo := surplus_ten h hc
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  omega

theorem monotone_twenty_three (C : Circuit) (hm : Monotone2 C) (hc : computes C) : 23 ≤ C.size := by
  obtain ⟨D, hd, hsize, hcomp⟩ := normalized C hm hc
  exact (length_twenty_three hd hcomp).trans hsize

theorem small_classification {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hs : D.length ≤ 24) :
    ∃ m ∈ elevenMasks, mask m = ineligSet 14 D ∧
      (Bplus 14 D ≤ 10 → m ∈ tenMasks) := by
  obtain ⟨m, enc⟩ := repr (ineligSet 14 D)
  have total := surplus_identity h
  rw [totalSurplus_split] at total
  have yes := possible_of h hc 11 m.val enc (by omega)
  have cls := all_classes m
  simp only [classTest, Bool.and_eq_true] at cls
  have eleven := cls.2
  simp only [yes, Bool.not_true, Bool.false_or, List.contains_iff_mem] at eleven
  refine ⟨m.val, eleven, enc, ?_⟩
  intro cap
  have ten := cls.1.2
  have yesTen := possible_of h hc 10 m.val enc cap
  simpa only [yesTen, Bool.not_true, Bool.false_or, List.contains_iff_mem] using ten

end PEqualNP.Outside.L_meta_9775.UpstreamCore
