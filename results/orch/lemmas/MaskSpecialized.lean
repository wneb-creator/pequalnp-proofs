import Init
abbrev Word := BitVec 512
def fits (mono desired ground sample : Bool) : Bool :=
 if mono then if desired then !ground || sample else !sample || ground else ground == sample
def pinMask (mono desired sample : Bool) (w : Word) : Word :=
 if fits mono desired false sample then
  if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
 else if fits mono desired true sample then w else 0
def maskUp : (ws : List Word) → (Fin ws.length → Bool) → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,x => if x 0 then w &&& maskUp ws (fun i => x i.succ) else maskUp ws (fun i => x i.succ)
def maskDown : (ws : List Word) → (Fin ws.length → Bool) → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,x => if x 0 then maskDown ws (fun i => x i.succ) else ~~~w &&& maskDown ws (fun i => x i.succ)
def maskExact : (ws : List Word) → (Fin ws.length → Bool) → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,x => (if x 0 then w else ~~~w) &&& maskExact ws (fun i => x i.succ)
def mask (mono desired : Bool) (ws : List Word) (x : Fin ws.length → Bool) : Word :=
 if mono then if desired then maskDown ws x else maskUp ws x else maskExact ws x
theorem mask_nil (mono desired : Bool) (x : Fin 0 → Bool) : mask mono desired [] x = BitVec.allOnes 512 := by
 cases mono <;> cases desired <;> rfl
set_option maxRecDepth 4096 in
theorem mask_cons (mono desired : Bool) (w : Word) (ws : List Word) (x : Fin (w::ws).length → Bool) :
 mask mono desired (w::ws) x = pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ) := by
 cases mono <;> cases desired <;> cases hx : x 0 <;> simp [mask,maskUp,maskDown,maskExact,pinMask,fits,hx] <;> exact BitVec.allOnes_and.symm
