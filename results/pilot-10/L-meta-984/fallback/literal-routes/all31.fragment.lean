def C0_literalRoutes : List (List (Nat × Nat)) := [[(0x20,2),(0xc,4),(0x10,2),(0x1054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x40,1),(0x20,2),(0xc,4),(0x10,2),(0x1115,1)],[(0x4000,1),(0xb02,4),(0x11,2),(0x4000,1)],[(0x4054,1),(0x30,2),(0xb06,4),(0x13,2),(0x4100,1)],[(0x4000,1),(0x20,2),(0xb09,4),(0x3,2),(0x5054,1)],[(0x4054,1),(0xb05,4),(0x2,2),(0x5154,1)]]

def C0_literalOri : List Nat → List Nat := literalRouteOrient C0_literalRoutes

theorem C0_literalGood : literalRoutesGood 0x7f00 C0_literalRoutes = true := by decide +kernel

theorem C0_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C0_literalOri ws) :=
  literalRouteOrient_run h C0_literalRoutes C0_literalGood

def C1_literalRoutes : List (List (Nat × Nat)) := [[(0x200,2),(0x100,4),(0x18,8),(0x10f,4),(0x221,2),(0x155,1)],[(0x210,2),(0x900,4),(0x90,8),(0x904,4),(0x212,2),(0x1000,1)],[(0x130,2),(0x6,8),(0x9,4),(0x103,2),(0x1155,1)],[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x544,1)],[(0x140,1),(0x200,2),(0x100,4),(0x18,8),(0x10f,4),(0x221,2),(0x415,1)],[(0x10,1),(0x300,2),(0xc00,4),(0xc0,8),(0xc02,4),(0x300,2),(0x1554,1)],[(0x140,1),(0x130,2),(0x6,8),(0x9,4),(0x103,2),(0x1415,1)],[(0x100,1),(0x1200,2),(0x800,4),(0x80,8),(0xe00,4),(0x1200,2),(0x4104,1)],[(0x4,1),(0x1200,2),(0x100,4),(0x18,8),(0x70f,4),(0x1221,2),(0x4151,1)],[(0x100,1),(0x1210,2),(0x800,4),(0x80,8),(0xe04,4),(0x1212,2),(0x4444,1)],[(0x4,1),(0x1200,2),(0x100,4),(0x18,8),(0x707,4),(0x1220,2),(0x4411,1)],[(0x104,1),(0x3010,2),(0x100,4),(0x10,8),(0xd04,4),(0x3012,2),(0x5040,1)],[(0x144,1),(0x2110,2),(0x6,8),(0x90b,4),(0x2100,2),(0x5151,1)],[(0x110,1),(0x2100,2),(0x400,4),(0x40,8),(0xd02,4),(0x2100,2),(0x5510,1)],[(0x144,1),(0x2130,2),(0x6,8),(0x909,4),(0x2103,2),(0x5411,1)]]

def C1_literalOri : List Nat → List Nat := literalRouteOrient C1_literalRoutes

theorem C1_literalGood : literalRoutesGood 0x1fc00 C1_literalRoutes = true := by decide +kernel

theorem C1_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fc00 s ws) :
    MonRun 0x1fc00 s (C1_literalOri ws) :=
  literalRouteOrient_run h C1_literalRoutes C1_literalGood

def C2_literalRoutes : List (List (Nat × Nat)) := [[(0x1000,1),(0x2030,2),(0x80c,4),(0x2030,2),(0x5000,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x300,2),(0x115,1)],[(0x1100,1),(0x2030,2),(0x200,4),(0x20,8),(0xa0c,4),(0x2130,2),(0x5115,1)]]

def C2_literalOri : List Nat → List Nat := literalRouteOrient C2_literalRoutes

theorem C2_literalGood : literalRoutesGood 0xfe00 C2_literalRoutes = true := by decide +kernel

theorem C2_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xfe00 s ws) :
    MonRun 0xfe00 s (C2_literalOri ws) :=
  literalRouteOrient_run h C2_literalRoutes C2_literalGood

def C3_literalRoutes : List (List (Nat × Nat)) := [[(0x4040,1),(0x1010,2),(0x404,4),(0x3232,2),(0x4040,1)]]

def C3_literalOri : List Nat → List Nat := literalRouteOrient C3_literalRoutes

theorem C3_literalGood : literalRoutesGood 0x7f00 C3_literalRoutes = true := by decide +kernel

theorem C3_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C3_literalOri ws) :=
  literalRouteOrient_run h C3_literalRoutes C3_literalGood

def C4_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C4_literalOri : List Nat → List Nat := literalRouteOrient C4_literalRoutes

theorem C4_literalGood : literalRoutesGood 0x7f00 C4_literalRoutes = true := by decide +kernel

theorem C4_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C4_literalOri ws) :=
  literalRouteOrient_run h C4_literalRoutes C4_literalGood

def C5_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x10,2),(0x4,4),(0x12,2),(0x144,1)]]

def C5_literalOri : List Nat → List Nat := literalRouteOrient C5_literalRoutes

theorem C5_literalGood : literalRoutesGood 0x7f00 C5_literalRoutes = true := by decide +kernel

theorem C5_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C5_literalOri ws) :=
  literalRouteOrient_run h C5_literalRoutes C5_literalGood

def C6_literalRoutes : List (List (Nat × Nat)) := [[(0x4140,1),(0x200,4),(0x20,8),(0x208,4),(0x2010,2),(0x4140,1)],[(0x10,2),(0x6,4),(0x13,2),(0x4015,1)],[(0x4100,1),(0x200,4),(0x20,8),(0x20e,4),(0x2013,2),(0x154,1)],[(0x100,2),(0x4,8),(0x7,4),(0x2132,2),(0x4015,1)],[(0x130,2),(0x4,8),(0x3,4),(0x2130,2)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x302,2),(0x114,1)],[(0x4404,1),(0x100,4),(0x10,8),(0x104,4),(0x2222,2),(0x4404,1)],[(0x110,1),(0x210,2),(0x800,4),(0x80,8),(0x806,4),(0x313,2),(0x4105,1)],[(0x4110,1),(0x200,4),(0x20,8),(0x20e,4),(0x2111,2),(0x144,1)],[(0x144,1),(0x2,8),(0xb,4),(0x2111,2),(0x4110,1)],[(0x104,1),(0x10,2),(0x2,8),(0x9,4),(0x2110,2),(0x114,1)]]

def C6_literalOri : List Nat → List Nat := literalRouteOrient C6_literalRoutes

theorem C6_literalGood : literalRoutesGood 0xfe00 C6_literalRoutes = true := by decide +kernel

theorem C6_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xfe00 s ws) :
    MonRun 0xfe00 s (C6_literalOri ws) :=
  literalRouteOrient_run h C6_literalRoutes C6_literalGood

def C7_literalRoutes : List (List (Nat × Nat)) := [[(0x1004,1),(0x2000,2),(0x800,4),(0x2032,2),(0x1104,1)]]

def C7_literalOri : List Nat → List Nat := literalRouteOrient C7_literalRoutes

theorem C7_literalGood : literalRoutesGood 0x7f00 C7_literalRoutes = true := by decide +kernel

theorem C7_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f00 s ws) :
    MonRun 0x7f00 s (C7_literalOri ws) :=
  literalRouteOrient_run h C7_literalRoutes C7_literalGood

def C8_literalRoutes : List (List (Nat × Nat)) := [[(0x450,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x1210,2),(0x450,1)],[(0x1515,1)],[(0x450,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x1210,2),(0x1145,1)],[(0x410,1),(0x2020,2),(0x200,4),(0x20,8),(0xa0d,4),(0x2120,2),(0x1105,1)],[(0x144,1),(0x2000,2),(0x400,4),(0x40,8),(0xd01,4),(0x2022,2),(0x144,1)],[(0x410,1),(0x2020,2),(0x200,4),(0x20,8),(0xa0d,4),(0x2120,2),(0x410,1)],[(0x144,1),(0x2000,2),(0x400,4),(0x40,8),(0xd01,4),(0x2022,2),(0x1451,1)],[(0x104,1),(0x1000,2),(0x800,4),(0x80,8),(0xe02,4),(0x1011,2),(0x1411,1)],[(0x40,1),(0x1000,2),(0x40,8),(0x20a,4),(0x1123,2),(0x40,1)],[(0x104,1),(0x1000,2),(0x800,4),(0x80,8),(0xe02,4),(0x1011,2),(0x104,1)],[(0x40,1),(0x1000,2),(0x40,8),(0x20a,4),(0x1123,2),(0x1555,1)],[(0x2000,2),(0x80,8),(0x105,4),(0x2213,2),(0x1515,1)],[(0x2000,2),(0x80,8),(0x105,4),(0x2213,2)]]

def C8_literalOri : List Nat → List Nat := literalRouteOrient C8_literalRoutes

theorem C8_literalGood : literalRoutesGood 0x3f80 C8_literalRoutes = true := by decide +kernel

theorem C8_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3f80 s ws) :
    MonRun 0x3f80 s (C8_literalOri ws) :=
  literalRouteOrient_run h C8_literalRoutes C8_literalGood

def C9_literalRoutes : List (List (Nat × Nat)) := [[(0x400,1),(0x200,2),(0x400,1)],[(0x100,1),(0x210,2),(0x800,4),(0x80,8),(0x804,4),(0x212,2),(0x100,1)],[(0x100,1),(0x210,2),(0x800,4),(0x80,8),(0x804,4),(0x312,2),(0x100,1)],[(0x44,1),(0x10,2),(0x4,4),(0x32,2),(0x44,1)],[(0x444,1),(0x10,2),(0x4,4),(0x232,2),(0x444,1)],[(0x110,1),(0x200,2),(0x800,4),(0x80,8),(0x802,4),(0x210,2),(0x114,1)],[(0x110,1),(0x200,2),(0x800,4),(0x80,8),(0x802,4),(0x310,2),(0x114,1)],[(0x1000,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2120,2),(0x1004,1)],[(0x400,1),(0x100,2),(0x400,4),(0x40,8),(0x500,4),(0x320,2),(0x404,1)],[(0x1140,1),(0x210,2),(0x800,4),(0x80,8),(0xa04,4),(0x232,2),(0x1104,1)],[(0x1140,1),(0x210,2),(0x800,4),(0x80,8),(0xa04,4),(0x332,2),(0x1104,1)],[(0x1104,1),(0x2010,2),(0x200,4),(0x20,8),(0xa04,4),(0x2032,2),(0x1140,1)],[(0x1104,1),(0x2010,2),(0x200,4),(0x20,8),(0xa04,4),(0x2132,2),(0x1140,1)],[(0x1010,1),(0x2000,2),(0x100,4),(0x10,8),(0x902,4),(0x2000,2),(0x1050,1)],[(0x410,1),(0x1000,2),(0x100,4),(0x10,8),(0x502,4),(0x1200,2),(0x450,1)]]

def C9_literalOri : List Nat → List Nat := literalRouteOrient C9_literalRoutes

theorem C9_literalGood : literalRoutesGood 0x1fe0 C9_literalRoutes = true := by decide +kernel

theorem C9_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C9_literalOri ws) :=
  literalRouteOrient_run h C9_literalRoutes C9_literalGood

def C10_literalRoutes : List (List (Nat × Nat)) := [[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)]]

def C10_literalOri : List Nat → List Nat := literalRouteOrient C10_literalRoutes

theorem C10_literalGood : literalRoutesGood 0x1fe0 C10_literalRoutes = true := by decide +kernel

theorem C10_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C10_literalOri ws) :=
  literalRouteOrient_run h C10_literalRoutes C10_literalGood

def C11_literalRoutes : List (List (Nat × Nat)) := [[(0x1000,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2123,2),(0x1000,1)],[(0x440,1),(0x100,2),(0x400,4),(0x40,8),(0x400,4),(0x320,2),(0x445,1)],[(0x1100,1),(0x2000,2),(0x200,4),(0x20,8),(0xa00,4),(0x2103,2),(0x1145,1)],[(0x4,1),(0x1000,2),(0x400,4),(0x1202,2),(0x4044,1)],[(0x1404,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2322,2),(0x5041,1)],[(0x1044,1),(0x100,2),(0x400,4),(0x40,8),(0x600,4),(0x321,2),(0x5401,1)],[(0x104,1),(0x200,4),(0x20,8),(0x300,4),(0x1,2),(0x4504,1)]]

def C11_literalOri : List Nat → List Nat := literalRouteOrient C11_literalRoutes

theorem C11_literalGood : literalRoutesGood 0x1fe00 C11_literalRoutes = true := by decide +kernel

theorem C11_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe00 s ws) :
    MonRun 0x1fe00 s (C11_literalOri ws) :=
  literalRouteOrient_run h C11_literalRoutes C11_literalGood

def C12_literalRoutes : List (List (Nat × Nat)) := [[(0x400,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x111,1)],[(0x110,1),(0x20,2),(0x200,4),(0x20,8),(0x208,4),(0x20,2),(0x511,1)]]

def C12_literalOri : List Nat → List Nat := literalRouteOrient C12_literalRoutes

theorem C12_literalGood : literalRoutesGood 0x1fe0 C12_literalRoutes = true := by decide +kernel

theorem C12_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C12_literalOri ws) :=
  literalRouteOrient_run h C12_literalRoutes C12_literalGood

def C13_literalRoutes : List (List (Nat × Nat)) := [[(0x440,1),(0x220,2),(0x445,1)],[(0x100,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x203,2),(0x1100,1)],[(0x440,1),(0x100,2),(0x400,4),(0x40,8),(0x400,4),(0x323,2),(0x1445,1)]]

def C13_literalOri : List Nat → List Nat := literalRouteOrient C13_literalRoutes

theorem C13_literalGood : literalRoutesGood 0x7f80 C13_literalRoutes = true := by decide +kernel

theorem C13_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C13_literalOri ws) :=
  literalRouteOrient_run h C13_literalRoutes C13_literalGood

def C14_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x100,2),(0x400,4),(0x40,8),(0x500,4),(0x322,2),(0x4,1)]]

def C14_literalOri : List Nat → List Nat := literalRouteOrient C14_literalRoutes

theorem C14_literalGood : literalRoutesGood 0x1fe0 C14_literalRoutes = true := by decide +kernel

theorem C14_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe0 s ws) :
    MonRun 0x1fe0 s (C14_literalOri ws) :=
  literalRouteOrient_run h C14_literalRoutes C14_literalGood

def C15_literalRoutes : List (List (Nat × Nat)) := [[(0x4,1),(0x32,2),(0x404,1)]]

def C15_literalOri : List Nat → List Nat := literalRouteOrient C15_literalRoutes

theorem C15_literalGood : literalRoutesGood 0xff00 C15_literalRoutes = true := by decide +kernel

theorem C15_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C15_literalOri ws) :=
  literalRouteOrient_run h C15_literalRoutes C15_literalGood

def C16_literalRoutes : List (List (Nat × Nat)) := []

def C16_literalOri : List Nat → List Nat := literalRouteOrient C16_literalRoutes

theorem C16_literalGood : literalRoutesGood 0x3fc0 C16_literalRoutes = true := by decide +kernel

theorem C16_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3fc0 s ws) :
    MonRun 0x3fc0 s (C16_literalOri ws) :=
  literalRouteOrient_run h C16_literalRoutes C16_literalGood

def C17_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4115,1)]]

def C17_literalOri : List Nat → List Nat := literalRouteOrient C17_literalRoutes

theorem C17_literalGood : literalRoutesGood 0xff00 C17_literalRoutes = true := by decide +kernel

theorem C17_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C17_literalOri ws) :=
  literalRouteOrient_run h C17_literalRoutes C17_literalGood

def C18_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4454,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x151,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4515,1)]]

def C18_literalOri : List Nat → List Nat := literalRouteOrient C18_literalRoutes

theorem C18_literalGood : literalRoutesGood 0xff00 C18_literalRoutes = true := by decide +kernel

theorem C18_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C18_literalOri ws) :=
  literalRouteOrient_run h C18_literalRoutes C18_literalGood

def C19_literalRoutes : List (List (Nat × Nat)) := [[(0x4044,1),(0x2322,2),(0x4044,1)]]

def C19_literalOri : List Nat → List Nat := literalRouteOrient C19_literalRoutes

theorem C19_literalGood : literalRoutesGood 0x7f80 C19_literalRoutes = true := by decide +kernel

theorem C19_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C19_literalOri ws) :=
  literalRouteOrient_run h C19_literalRoutes C19_literalGood

def C20_literalRoutes : List (List (Nat × Nat)) := []

def C20_literalOri : List Nat → List Nat := literalRouteOrient C20_literalRoutes

theorem C20_literalGood : literalRoutesGood 0x7f80 C20_literalRoutes = true := by decide +kernel

theorem C20_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C20_literalOri ws) :=
  literalRouteOrient_run h C20_literalRoutes C20_literalGood

def C21_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)]]

def C21_literalOri : List Nat → List Nat := literalRouteOrient C21_literalRoutes

theorem C21_literalGood : literalRoutesGood 0xff00 C21_literalRoutes = true := by decide +kernel

theorem C21_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff00 s ws) :
    MonRun 0xff00 s (C21_literalOri ws) :=
  literalRouteOrient_run h C21_literalRoutes C21_literalGood

def C22_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x200,4),(0x20,8),(0xa08,4),(0x2120,2),(0x1011,1)]]

def C22_literalOri : List Nat → List Nat := literalRouteOrient C22_literalRoutes

theorem C22_literalGood : literalRoutesGood 0x3fc0 C22_literalRoutes = true := by decide +kernel

theorem C22_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3fc0 s ws) :
    MonRun 0x3fc0 s (C22_literalOri ws) :=
  literalRouteOrient_run h C22_literalRoutes C22_literalGood

def C23_literalRoutes : List (List (Nat × Nat)) := [[(0x50,1),(0x10,2),(0xe,4),(0x310,2),(0x1050,1)]]

def C23_literalOri : List Nat → List Nat := literalRouteOrient C23_literalRoutes

theorem C23_literalGood : literalRoutesGood 0x7f80 C23_literalRoutes = true := by decide +kernel

theorem C23_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C23_literalOri ws) :=
  literalRouteOrient_run h C23_literalRoutes C23_literalGood

def C24_literalRoutes : List (List (Nat × Nat)) := [[(0x140,1),(0x200,4),(0x20,8),(0x208,4),(0x10,2),(0x4140,1)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0x800,4),(0x302,2),(0x114,1)],[(0x404,1),(0x100,4),(0x10,8),(0x104,4),(0x222,2),(0x4404,1)],[(0x4000,1),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e04,4),(0x2222,2),(0x4000,1)],[(0x54,1),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xf08,4),(0x2212,2),(0x4040,1)],[(0x4040,1),(0x11120,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xf02,4),(0x13332,2),(0x54,1)],[(0x40,1),(0x20,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xf02,4),(0x2220,2),(0x44,1)]]

def C24_literalOri : List Nat → List Nat := literalRouteOrient C24_literalRoutes

theorem C24_literalGood : literalRoutesGood 0x1fe00 C24_literalRoutes = true := by decide +kernel

theorem C24_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1fe00 s ws) :
    MonRun 0x1fe00 s (C24_literalOri ws) :=
  literalRouteOrient_run h C24_literalRoutes C24_literalGood

def C25_literalRoutes : List (List (Nat × Nat)) := [[(0x1010,1),(0x2020,2),(0x808,4),(0x3020,2),(0x1110,1)],[(0x5400,1),(0x220,2),(0x200,4),(0x20,8),(0xb0d,4),(0x231,2),(0x5414,1)],[(0x410,1),(0x800,4),(0x80,8),(0xf05,4),(0x1111,2),(0x410,1)]]

def C25_literalOri : List Nat → List Nat := literalRouteOrient C25_literalRoutes

theorem C25_literalGood : literalRoutesGood 0x7f80 C25_literalRoutes = true := by decide +kernel

theorem C25_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x7f80 s ws) :
    MonRun 0x7f80 s (C25_literalOri ws) :=
  literalRouteOrient_run h C25_literalRoutes C25_literalGood

def C26_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x100,4),(0x10,8),(0x10e,4),(0x2000,2),(0x4000,1)],[(0x1000,1),(0x2010,2),(0x100,4),(0x10,8),(0x904,4),(0x2032,2),(0x1000,1)],[(0x1000,1),(0x2100,2),(0x4,8),(0x80a,4),(0x3132,2),(0x1000,1)],[(0x2020,2),(0x808,4),(0x3030,2),(0x10000,1)],[(0x5000,1),(0x20,2),(0x100,4),(0x10,8),(0x90c,4),(0x2012,2),(0x14000,1)],[(0x4000,1),(0x2030,2),(0x100,4),(0x10,8),(0x906,4),(0x2,2),(0x15000,1)],[(0x4000,1),(0x120,2),(0x4,8),(0x802,4),(0x120,2),(0x15000,1)],[(0x444,1),(0x10,2),(0x100,4),(0x10,8),(0x104,4),(0x232,2),(0x444,1)],[(0x4444,1),(0x100,2),(0x4,8),(0xa,4),(0x2332,2),(0x4444,1)],[(0x410,1),(0x1000,2),(0x100,4),(0x10,8),(0x502,4),(0x1200,2),(0x454,1)],[(0x1100,1),(0x2000,2),(0x2,8),(0x80c,4),(0x3100,2),(0x1154,1)],[(0x104,1),(0x200,2),(0x800,4),(0x80,8),(0xa04,4),(0x1302,2),(0x10114,1)],[(0x454,1),(0x1130,2),(0x4,8),(0x106,4),(0x310,2),(0x11410,1)],[(0x1410,1),(0x110,2),(0x400,4),(0x40,8),(0x506,4),(0x1330,2),(0x10454,1)],[(0x4100,1),(0x10,2),(0x2,8),(0x80c,4),(0x120,2),(0x15154,1)],[(0x10000,1),(0x21000,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80400,4),(0x21200,2),(0x10044,1)],[(0x4000,1),(0x1000,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0x50e,4),(0x3200,2),(0x4044,1)],[(0x11400,1),(0x2010,2),(0x20100,4),(0x200000,8),(0x2000,16),(0x200010,8),(0x20904,4),(0x2232,2),(0x11044,1)],[(0x11400,1),(0x2100,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200004,8),(0x2080a,4),(0x3332,2),(0x11044,1)],[(0x2020,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200000,8),(0x20c08,4),(0x3230,2),(0x10044,1)],[(0x15000,1),(0x1020,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0xd0c,4),(0x3212,2),(0x4044,1)],[(0x400,1),(0x2030,2),(0x20100,4),(0x200000,8),(0x2000,16),(0x200010,8),(0x20d06,4),(0x2202,2),(0x11044,1)],[(0x15000,1),(0x10120,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40902,4),(0x10320,2),(0x4044,1)],[(0x11044,1),(0x20010,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x80304,4),(0x20232,2),(0x11400,1)],[(0x11044,1),(0x20100,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800004,8),(0x8020a,4),(0x21332,2),(0x11400,1)],[(0x11010,1),(0x20000,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x80302,4),(0x20000,2),(0x11410,1)],[(0x4100,1),(0x10000,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400002,8),(0x4010c,4),(0x12000,2),(0x4510,1)],[(0x15104,1),(0x12200,2),(0x40800,4),(0x400000,8),(0x4000,16),(0x400080,8),(0x40b04,4),(0x10202,2),(0x4550,1)],[(0x15454,1),(0x12130,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40306,4),(0x10110,2),(0x5054,1)],[(0x14010,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xe06,4),(0x10130,2),(0x5410,1)],[(0x1500,1),(0x20010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800002,8),(0x8050c,4),(0x20120,2),(0x10110,1)],[(0x10010,1),(0x21010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80604,4),(0x20230,2),(0x54,1)],[(0x11044,1),(0x20020,2),(0x80100,4),(0x800000,8),(0x8000,16),(0x800010,8),(0x8070c,4),(0x20212,2),(0x400,1)],[(0x4540,1),(0x10200,2),(0x40800,4),(0x400000,8),(0x4000,16),(0x400080,8),(0x40b04,4),(0x12202,2),(0x15114,1)],[(0x11010,1),(0x21130,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800004,8),(0x80306,4),(0x21110,2),(0x410,1)],[(0x10,1),(0x20010,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800000,8),(0x80604,4),(0x20030,2),(0x10,1)],[(0x14444,1),(0x10020,2),(0x40100,4),(0x400000,8),(0x4000,16),(0x400010,8),(0x40b0c,4),(0x10212,2),(0x14444,1)],[(0x1140,1),(0x20200,2),(0x800,4),(0x80000,8),(0x800,16),(0x80080,8),(0xf04,4),(0x20202,2),(0x1150,1)],[(0x14410,1),(0x10130,2),(0x40000,4),(0x400000,8),(0x4000,16),(0x400004,8),(0x40b06,4),(0x10310,2),(0x14454,1)],[(0x4044,1),(0x1030,2),(0x100,4),(0x10000,8),(0x100,16),(0x10010,8),(0x706,4),(0x3202,2),(0x15000,1)],[(0x11540,1),(0x21220,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800008,8),(0x80302,4),(0x21320,2),(0x504,1)],[(0x5054,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0x706,4),(0x12130,2),(0x15454,1)],[(0x10110,1),(0x20020,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800002,8),(0x8050c,4),(0x21010,2),(0x1500,1)],[(0x14444,1),(0x10030,2),(0x40100,4),(0x400000,8),(0x4000,16),(0x400010,8),(0x40b06,4),(0x12002,2),(0x14444,1)],[(0x1140,1),(0x20220,2),(0x80000,4),(0x800000,8),(0x8000,16),(0x800008,8),(0x80502,4),(0x21320,2),(0x1140,1)],[(0x14054,1),(0x10110,2),(0x400,4),(0x40000,8),(0x400,16),(0x40040,8),(0xf06,4),(0x12130,2),(0x15410,1)],[(0x110,1),(0x2020,2),(0x20000,4),(0x200000,8),(0x2000,16),(0x200002,8),(0x20d0c,4),(0x3110,2),(0x1544,1)]]

def C26_literalOri : List Nat → List Nat := literalRouteOrient C26_literalRoutes

theorem C26_literalGood : literalRoutesGood 0x3fe00 C26_literalRoutes = true := by decide +kernel

theorem C26_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x3fe00 s ws) :
    MonRun 0x3fe00 s (C26_literalOri ws) :=
  literalRouteOrient_run h C26_literalRoutes C26_literalGood

def C27_literalRoutes : List (List (Nat × Nat)) := [[(0x4000,1),(0x20,2),(0xc,4),(0x2010,2),(0x4054,1)],[(0x10,1),(0x20,2),(0x8,4),(0x20,2),(0x451,1)],[(0x4040,1),(0x20,2),(0xc,4),(0x2010,2),(0x4415,1)],[(0x5000,1),(0x1000,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e02,4),(0x1011,2),(0x5000,1)],[(0x5054,1),(0x1030,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e06,4),(0x1013,2),(0x5400,1)],[(0x5400,1),(0x1020,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e09,4),(0x1003,2),(0x5054,1)],[(0x5454,1),(0x1000,2),(0x10000,4),(0x100000,8),(0x1000,16),(0x100000,8),(0x10e05,4),(0x1002,2),(0x5454,1)]]

def C27_literalOri : List Nat → List Nat := literalRouteOrient C27_literalRoutes

theorem C27_literalGood : literalRoutesGood 0x1ff00 C27_literalRoutes = true := by decide +kernel

theorem C27_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1ff00 s ws) :
    MonRun 0x1ff00 s (C27_literalOri ws) :=
  literalRouteOrient_run h C27_literalRoutes C27_literalGood

def C28_literalRoutes : List (List (Nat × Nat)) := [[(0x5550,1),(0x1010,2),(0x100,4),(0x10,8),(0x50e,4),(0x3210,2),(0x5550,1)]]

def C28_literalOri : List Nat → List Nat := literalRouteOrient C28_literalRoutes

theorem C28_literalGood : literalRoutesGood 0xff80 C28_literalRoutes = true := by decide +kernel

theorem C28_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff80 s ws) :
    MonRun 0xff80 s (C28_literalOri ws) :=
  literalRouteOrient_run h C28_literalRoutes C28_literalGood

def C29_literalRoutes : List (List (Nat × Nat)) := [[(0x1040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x2120,2),(0x5041,1)],[(0x4004,1),(0x2302,2),(0x4014,1)],[(0x5040,1),(0x2100,2),(0x400,4),(0x40,8),(0xc00,4),(0x3221,2),(0x1051,1)],[(0x1404,1),(0x800,4),(0x80,8),(0xa00,4),(0x1312,2),(0x5115,1)],[(0x5400,1),(0x800,4),(0x80,8),(0xa00,4),(0x1011,2),(0x5400,1)]]

def C29_literalOri : List Nat → List Nat := literalRouteOrient C29_literalRoutes

theorem C29_literalGood : literalRoutesGood 0xff80 C29_literalRoutes = true := by decide +kernel

theorem C29_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0xff80 s ws) :
    MonRun 0xff80 s (C29_literalOri ws) :=
  literalRouteOrient_run h C29_literalRoutes C29_literalGood

def C30_literalRoutes : List (List (Nat × Nat)) := [[(0x10040,1),(0x21020,2),(0x80000,8),(0x800,16),(0x80000,8),(0x302,4),(0x22021,2),(0x15150,1)]]

def C30_literalOri : List Nat → List Nat := literalRouteOrient C30_literalRoutes

theorem C30_literalGood : literalRoutesGood 0x1ff00 C30_literalRoutes = true := by decide +kernel

theorem C30_literalOri_run {s : Nat} {ws : List Nat} (h : MonRun 0x1ff00 s ws) :
    MonRun 0x1ff00 s (C30_literalOri ws) :=
  literalRouteOrient_run h C30_literalRoutes C30_literalGood
