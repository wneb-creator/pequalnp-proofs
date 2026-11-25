import PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case1 : chk [] (pr ac4 0) 0 12 1 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case2 : chk [] (pr ac4 0) 0 12 2 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case3 : chk [] (pr ac4 0) 0 12 3 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case4 : chk [] (pr ac4 0) 0 12 4 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case5 : chk [] (pr ac4 0) 0 12 5 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case6 : chk [] (pr ac4 0) 0 12 6 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case7 : chk [] (pr ac4 0) 0 12 7 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case8 : chk [] (pr ac4 0) 0 12 8 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case9 : chk [] (pr ac4 0) 0 12 9 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case10 : chk [] (pr ac4 0) 0 12 10 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case11 : chk [] (pr ac4 0) 0 12 11 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def lower13Case12 : chk [] (pr ac4 0) 0 12 12 FF 1 = false := by decide +kernel

example (lower13Case0 : chk [] (pr ac4 0) 0 12 0 FF 1 = false) : m0_0.all (okS ac4 0 12) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  simp only [m0_0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [okS, Bool.not_eq_true'] using lower13Case0
  · simpa only [okS, Bool.not_eq_true'] using lower13Case1
  · simpa only [okS, Bool.not_eq_true'] using lower13Case2
  · simpa only [okS, Bool.not_eq_true'] using lower13Case3
  · simpa only [okS, Bool.not_eq_true'] using lower13Case4
  · simpa only [okS, Bool.not_eq_true'] using lower13Case5
  · simpa only [okS, Bool.not_eq_true'] using lower13Case6
  · simpa only [okS, Bool.not_eq_true'] using lower13Case7
  · simpa only [okS, Bool.not_eq_true'] using lower13Case8
  · simpa only [okS, Bool.not_eq_true'] using lower13Case9
  · simpa only [okS, Bool.not_eq_true'] using lower13Case10
  · simpa only [okS, Bool.not_eq_true'] using lower13Case11
  · simpa only [okS, Bool.not_eq_true'] using lower13Case12

end PEqualNP.Outside.L_meta_10760
