import PEqualNP.Defs
namespace OfficialEncodingCheck
section formula
variable (n s : ℕ)

/-- The width of one block of variables. -/
def wd : ℕ := 2 ^ n + n + s + 2

/-- Variable `(kd * (s + 1) + j) * wd + a`. -/
def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

/-- The literal "variable `v` is true" (`v + 1` in the checker's numbering, `2 (v + 1)`). -/
def P (v : ℕ) : ℕ := 2 * v + 2
/-- The literal "variable `v` is false". -/
def Q (v : ℕ) : ℕ := 2 * v + 3
/-- The literal saying variable `v` has value `b`. -/
def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

/-- Ordered pairs below `m`. -/
def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

/-- At least one operation per gate. -/
def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2),
    P (ix n s 0 j 3)]

/-- At least one source per gate and side. -/
def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

/-- The value of source `e` of gate `j` on row `r` is the value of the wire it reads. -/
def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

/-- The value of gate `j` on row `r` is its operation on its source values. -/
def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)],
   [Q (ix n s 0 j 3), P (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 3), Q (ix n s 3 j r), Q (ix n s 4 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

/-- At least one output source. -/
def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

/-- The output source carries `g` on row `r`. -/
def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

/-- Normal form: the output is the last wire, or the last gate is padding. -/
def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

/-- Normal form: padding is exactly `(TRUE, F, F)`; a gate that is not padding is not `TRUE`
and reads no `F`. -/
def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

/-- Normal form: the padding gates come first. -/
def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

/-- Normal form: no gate reads a padding wire. -/
def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

/-- A NOT gate has equal sources. -/
def fNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).map fun k =>
    [Q (ix n s 0 j 3), Q (ix n s 1 j k), P (ix n s 2 j k)]

/-- Normal form: no NOT gate reads a NOT gate. -/
def fNotNot : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).map fun i =>
    [Q (ix n s 0 j 3), Q (ix n s 0 i 3), Q (ix n s 1 j (n + i))]

/-- Normal form: a gate that is not padding has its first source below its second, or is a NOT. -/
def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l =>
      [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)] ++
        if l = k then [P (ix n s 0 j 3)] else []

/-- Normal form: a gate before the last that is not padding is read by a later gate. -/
def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

/-- The formula: a circuit of AND, OR and NOT gates with `s` gates (padding allowed) on `n` inputs,
in normal form, computing `g` on every row of `rows`. -/
def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s ++ fNot n s ++ fNotNot n s

end formula
section formula
variable (n s : ℕ)

/-- The escape literals of the order at `j`: gate `j` is padding, or gate `j + 1` reads `n + j`. -/
def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

/-- The order: unless gate `j` is padding or gate `j + 1` reads wire `n + j`, the triple
`(s1, s2, op)` of gate `j` is lexicographically below that of gate `j + 1`. -/
def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

/-- The formula `enc` with the order of adjacent independent gates. -/
def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

def edges : List (Nat × Nat) :=
  [(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),
   (4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def target (r : Nat) : Bool := edges.any fun e => r.testBit e.1 && r.testBit e.2
def rows : List Nat := (List.range 16384).filter fun r =>
  !target r || edges.any (fun e => r == 2^e.1 + 2^e.2)
def cnf : List (List Nat) := enc2 14 24 target rows
end OfficialEncodingCheck

def main : IO Unit := do
  IO.println "p cnf 3251953 1466230"
  for clause in OfficialEncodingCheck.cnf do
    IO.println (String.intercalate " " (clause.map fun l =>
      if l % 2 == 0 then toString (l / 2) else "-" ++ toString (l / 2)) ++ " 0")
