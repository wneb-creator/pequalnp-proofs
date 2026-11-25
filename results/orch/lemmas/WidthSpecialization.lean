import PetersenSeventeenFull
import WidthPrototype

namespace PEqualNP.Outside.L_meta_2373

example : WidthPrototype.zero (width := 511) = NineSigned.zero := rfl
example : WidthPrototype.one (width := 511) = NineSigned.one := rfl
example : WidthPrototype.bin (width := 511) = NineSigned.bin := rfl
example (u) (T : NineSigned.Sig) (k S) :
    WidthPrototype.Live (width := 511) u T k S ↔ NineSigned.Live u T k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [WidthPrototype.Live, NineSigned.Live, ih]; rfl
example : WidthPrototype.nrm (width := 511) = NineSigned.nrm := rfl
example : WidthPrototype.gv (width := 511) = NineSigned.gv := rfl
example : WidthPrototype.execute (width := 511) = NineSigned.execute := rfl
example {R : Type} (u) (roots : List (NineSigned.Wire R)) (p bank) :
    WidthPrototype.Reach u roots p bank ↔ NineSigned.Reach u roots p bank := by
  induction p generalizing bank with
  | zero => rfl
  | succ p ih => simp only [WidthPrototype.Reach, NineSigned.Reach, ih]; rfl
example {R : Type} (u) (goal : NineSigned.Wire R) (k ws) :
    WidthPrototype.Run u goal k ws ↔ NineSigned.Run u goal k ws := by
  induction k generalizing ws with
  | zero => rfl
  | succ k ih => simp only [WidthPrototype.Run, NineSigned.Run, ih]; rfl
example : WidthPrototype.table (width := 511) = NineSigned.table := rfl
example : WidthPrototype.observe (width := 511) = NineSigned.observe := rfl

example : WidthPrototype.zero (width := 1023) = Live1024.zero := rfl
example : WidthPrototype.one (width := 1023) = Live1024.one := rfl
example : WidthPrototype.bin (width := 1023) = Live1024.bin := rfl
example (u) (T : Live1024.Sig) (k S) :
    WidthPrototype.Live (width := 1023) u T k S ↔ Live1024.Live u T k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => simp only [WidthPrototype.Live, Live1024.Live, ih]; rfl
example : WidthPrototype.nrm (width := 1023) = Live1024.nrm := rfl
example : WidthPrototype.gv (width := 1023) = Live1024.gv := rfl
example : WidthPrototype.execute (width := 1023) = Live1024.execute := rfl
example {R : Type} (u) (roots : List (Live1024.Wire R)) (p bank) :
    WidthPrototype.Reach u roots p bank ↔ Live1024.Reach u roots p bank := by
  induction p generalizing bank with
  | zero => rfl
  | succ p ih => simp only [WidthPrototype.Reach, Live1024.Reach, ih]; rfl
example {R : Type} (u) (goal : Live1024.Wire R) (k ws) :
    WidthPrototype.Run u goal k ws ↔ Live1024.Run u goal k ws := by
  induction k generalizing ws with
  | zero => rfl
  | succ k ih => simp only [WidthPrototype.Run, Live1024.Run, ih]; rfl
example : WidthPrototype.table (width := 1023) = Live1024.table := rfl
example : WidthPrototype.observe (width := 1023) = Live1024.observe := rfl

end PEqualNP.Outside.L_meta_2373
