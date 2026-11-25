/-
The verifier half of the checker. Run by tools/check-lean.mjs, after the lemma file has been
built, as:

  lake exe checklemma <module> <statement file> <check|refute|reduce>

It never trusts what the lemma file printed or how it was elaborated. It reads the compiled
result and decides four things:

1. KERNEL. Every constant of every project module the lemma rests on is sent to the kernel
   again: the definitions root on top of the pinned modules it imports, everything else on top
   of the whole pinned library and the definitions root. A declaration that reached the
   compiled file without the kernel's agreement is refused here, and so is a project
   declaration that carries a name the pinned library or the definitions root already uses
   (but for a second copy of one of their theorems, same statement, which is left out: see
   `sameTheorem`).
2. THEOREM. The module declares a theorem whose name is the module's name.
3. AXIOMS. The theorem's transitive axioms, walked over the re-checked constants (not read from
   any cache the file could write), are inside the allowlist. `sorry` is the axiom `sorryAx`,
   so a `sorry` anywhere under the theorem is caught here, from the compiled proof.
4. STATEMENT. The recorded statement is elaborated in an environment made of the pinned
   library and the definitions root (`PEqualNP.Defs` and the modules under it) and nothing else
   of this project, whatever the lemma file imports. So nothing the lemma file or any helper
   module declares (an instance, a notation, a macro) can change what the text means, and a
   statement can only speak of the pinned library and the definitions root. The kernel then
   checks that the theorem is a proof of that statement (of its negation for `refute`), in an
   environment that extends the one the statement was read in.

For `reduce` (the decomposition door, ships dark) it also decides, in `reduceShape`: the theorem
is `T1 → ... → Tk → S`, 2 ≤ k ≤ 4 non-dependent arrows, the conclusion structurally the recorded
statement, each child a closed proposition of the statement environment, distinct, not `S`, not
`False`, and the module declares nothing but the theorem; each child is printed by Lean and read
back to the same term before its `CHILD` line is printed. Two screens on each child: TEXT (class
`reduce-child`: no string or name literal, no text type such as `String`, `Char`, `Lean.Name`
among its constants or their types, no constant of the meta namespaces `Lean`, `Std.Format`,
`IO` under it, no metadata node, at most 2000 printed characters) and WASTE (class
`reduce-waste`: the recorded statement is not a subterm of it, and `decide` of it, where an
instance exists, does not evaluate to `false` within a small budget).

On acceptance it also prints `MODULES` (every project module the theorem rests on) and `DEFS`
(the modules of the definitions root), which the wrapper turns into hashes for the artifact.

Exit 0: accepted. Exit 1: rejected, with one REJECTED line naming the class. Exit 3: the
verifier itself could not run.
-/
import Lean
open Lean

namespace PEqualNPChecker

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Roots of the libraries this project owns (lean/lakefile.toml). Everything else is a pinned dependency. -/
def projectRoots : List Name := [`PEqualNP, `CheckerSuite]

def isProject (m : Name) : Bool := projectRoots.contains m.getRoot

/-- The definitions root: the one part of this project a recorded statement may speak of. -/
def defsRoot : Name := `PEqualNP.Defs

def isDefs (m : Name) : Bool := m == defsRoot || defsRoot.isPrefixOf m

/-- The pinned library a statement is read against, always the whole of it. -/
def statementLibrary : Name := `Mathlib

structure Walk where
  seen : NameSet := {}
  axioms : Array Name := #[]
  missing : Array Name := #[]

partial def walk (find : Name → Option ConstantInfo) (n : Name) : StateM Walk Unit := do
  if (← get).seen.contains n then return
  modify fun s => { s with seen := s.seen.insert n }
  match find n with
  | none => modify fun s => { s with missing := s.missing.push n }
  | some ci =>
    if ci matches .axiomInfo _ then modify fun s => { s with axioms := s.axioms.push n }
    for c in ci.getUsedConstantsAsSet do walk find c

def reject (cls msg : String) : IO UInt32 := do
  -- One line, always the last one printed: readers show the tail of the output.
  IO.println s!"REJECTED ({cls}): {msg.replace "\n" " "}"
  return 1

/-- No project module may declare a constant under this namespace: it is the checker's own. -/
def reserved : Name := `PEqualNPChecker

/-- A project constant `c` that carries the name of a constant `l` of the statement environment
is refused, with one exception, decided here: both are theorems, with the same universe
parameters and the same type. Lean writes some theorems on demand, in whichever module first
needs them (the equation lemmas `f.eq_1`, `f.eq_def`, ...): a project file that needs one and
does not import the pinned module that already holds it gets a second copy of its own, through
no act of its author.

Such a `c` is not accepted in place of `l`. It is LEFT OUT: it never reaches the kernel and never
enters the environment anything is checked in. Why nothing is lost:

* Every project constant that is kept is sent to the kernel on top of the statement environment,
  and there the name is `l`, the library's own theorem, with the library's own proof. Whatever
  `c`'s body says is never read by anything. So the final environment is the statement
  environment extended by kernel-accepted declarations only, as before; leaving a declaration
  out of the replay can only make the kernel refuse more (a kept constant that needed something
  `l` does not give), never accept more.
* A name still means one thing for the statement and for the proof: the name is `l` in both.
* The test is not what makes this sound (the point above holds for any left-out constant); it is
  what keeps the exception narrow. A term that names a theorem type-checks from its universe
  parameters and its type alone, and those are `l`'s exactly, so the honest file checks against
  `l` as it did against `c`. Everything else that collides is refused as before: a definition,
  an opaque, an axiom, an inductive type, a constructor, a recursor, a quotient constant on
  either side, a theorem whose type or universe parameters differ, a theorem against a
  non-theorem. `==` on `Expr` is equality up to bound variable names and binder annotations,
  neither of which the kernel reads; universe levels and constant names are compared exactly. -/
def sameTheorem (c l : ConstantInfo) : Bool :=
  match c, l with
  | .thmInfo c, .thmInfo l => c.levelParams == l.levelParams && c.type == l.type
  | _, _ => false

/-! ## The kind `reduce`: the runner side of the decomposition door.

A reduction file holds one theorem `M : T1 → ... → Tk → S`, 2 ≤ k ≤ 4, non-dependent arrows, `S`
the recorded statement. The `Ti` are the children: new steps the desk will post. `reduceShape`
decides everything the kind adds to `check`; the kernel check of `M` against `T1 → ... → Tk → S`
is the same one `check` runs. -/

def leadingForalls : Expr → Nat
  | .forallE _ _ b _ => leadingForalls b + 1
  | _ => 0

/-- The names of the bound variables inside a child are text of the file: they are replaced by
`x1, x2, ...` (by depth) before the child is printed. `==` does not read them. -/
partial def canonBinders (e : Expr) (d : Nat := 0) : Expr :=
  let x := Name.mkSimple s!"x{d + 1}"
  match e with
  | .forallE _ t b bi => .forallE x (canonBinders t d) (canonBinders b (d + 1)) bi
  | .lam _ t b bi => .lam x (canonBinders t d) (canonBinders b (d + 1)) bi
  | .letE _ t v b nd => .letE x (canonBinders t d) (canonBinders v d) (canonBinders b (d + 1)) nd
  | .app f a => .app (canonBinders f d) (canonBinders a d)
  | .mdata m b => .mdata m (canonBinders b d)
  | .proj s i b => .proj s i (canonBinders b d)
  | e => e

/-- How a child is printed: full names, the types of binders and numerals, proofs in full. -/
def childPpOptions : Options := Id.run do
  let mut o : Options := {}
  for n in [`pp.fullNames, `pp.funBinderTypes, `pp.numericTypes, `pp.proofs,
            `pp.structureInstanceTypes, `pp.letVarTypes] do
    o := o.setBool n true
  return o

def runMetaIn (env : Environment) (x : MetaM α) : IO α := do
  let ctx : Core.Context := { fileName := "<reduce>", fileMap := default, options := childPpOptions }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- A constant of the judged module that Lean wrote for the theorem itself, not one its author
declared: a matcher of a `match` in the proof (and its splitter and equations), or a theorem
whose last name component is internal (an auxiliary lemma). -/
def generatedFor (env : Environment) (mod : Name) (c : ConstantInfo) : Bool :=
  mod.isPrefixOf c.name && c.name != mod &&
    (Meta.isMatcherCore env c.name ||
     (match c.name with
      | .str p _ => Meta.isMatcherCore env p || (Meta.isMatcherCore env p.getPrefix && !p.isAnonymous)
      | _ => false) ||
     (c matches .thmInfo _ && c.name.isInternal))

/-- The types that carry text. A child may not mention one (red team, pre-switch-on item A):
outside prose must never reach the desk dressed as a child statement. -/
def textTypes : List Name :=
  [`String, `Char, `Lean.Name, `Substring, `Substring.Raw, `String.Pos, `String.Pos.Raw,
   `String.Slice, `String.Iterator]

/-- The longest printed child, in characters. -/
def maxChildChars : Nat := 2000

/-- A constant of `t` that is a text type, or whose type mentions one (so `String.length`,
`Char.ofNat`, `Nat.toDigits` are caught without the type's name appearing in `t` itself). -/
def textConstant (env : Environment) (t : Expr) : Option (Name × Name) := Id.run do
  for c in t.getUsedConstants do
    if textTypes.contains c then return some (c, c)
    if let some ci := env.find? c then
      for d in ci.type.getUsedConstants do
        if textTypes.contains d then return some (c, d)
  return none

/-- The namespaces of Lean's own meta types (red team, last runner-side items): `Lean.Expr`,
`Lean.Syntax`, `Std.Format`, `IO` and their kin carry text and code, so a child may not rest on
them (`∀ e : Lean.Expr, e = e` would otherwise travel). -/
def metaRoots : List Name := [`Lean, `Std.Format, `Std.ToFormat, `IO, `EIO, `BaseIO]

def isMetaName (n : Name) : Bool := metaRoots.any (·.isPrefixOf n)

/-- `e` with the tactic script of every `autoParam α stx` dropped (only `α` kept). The script is
syntax Lean stores for the elaborator (`Lean.Syntax`, `Lean.Name`); the kernel reads `α`. -/
partial def dropAutoParamScripts (e : Expr) : Expr :=
  e.replace fun s =>
    if s.isAppOfArity ``autoParam 2 then some (dropAutoParamScripts s.appFn!.appArg!) else none

/-- A meta-namespace constant the child rests on, with the constant of the child the walk
started from. The walk is the dependency walk of `walk` with two cuts, both of things that
cannot carry a child's meaning: the values (proofs) of theorems, and the tactic scripts of
`autoParam`s in library declarations (the child's own term is read whole). Without the cuts,
`P ⊆ NP` reaches `Lean.Omega` through proofs and `Real.sqrt` reaches `Lean.Syntax` through
autoParam scripts. Constructors of inductive types are walked. -/
def metaConstant (env : Environment) (t : Expr) : Option (Name × Name) := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array (Name × Name) := t.getUsedConstants.reverse.map fun c => (c, c)
  while todo.size > 0 do
    let (c0, n) := todo[todo.size - 1]!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if isMetaName n then return some (c0, n)
    let some ci := env.find? n | continue
    let es := match ci with
      | .thmInfo _ => #[ci.type]
      | _ => #[ci.type] ++ ci.value?.toArray
    for e in es do
      for c in (dropAutoParamScripts e).getUsedConstants do
        unless seen.contains c do todo := todo.push (c0, c)
    if let .inductInfo v := ci then
      for c in v.ctors do todo := todo.push (c0, c)
  return none

/-- Does `decide t` evaluate to `false`? The evaluation is `whnf` at full transparency in
`MetaM`, under a small heartbeat budget; a `false` it finds is then confirmed by the kernel
(`Kernel.isDefEq (decide t) false`). No instance, a stuck term, an exhausted budget, an error,
or a kernel that does not agree: the answer is no. -/
def decidesFalse (env : Environment) (t : Expr) : IO Bool := do
  let r ← (runMetaIn env do
      let now ← IO.getNumHeartbeats
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000, initHeartbeats := now }) do
        let some inst ← Meta.synthInstance? (mkApp (mkConst ``Decidable) t) | return none
        let d := mkApp2 (mkConst ``Decidable.decide) t inst
        let v ← Meta.withTransparency .all (Meta.whnf d)
        return some (d, v)).toBaseIO
  let .ok (some (d, v)) := r | return false
  unless v == mkConst ``Bool.false do return false
  match Kernel.isDefEq env {} d (mkConst ``Bool.false) with
  | .ok b => return b
  | .error _ => return false

/-- Everything `reduce` adds to `check`. On success, the children with the text each is
printed as (which has been parsed and elaborated again and found structurally equal). -/
unsafe def reduceShape (stmtEnv full : Environment) (libEnv : Kernel.Environment)
    (checked : Name → Option ConstantInfo) (mod : Name) (thm : TheoremVal) (recorded : Expr) :
    IO (Except (String × String) (Array (Expr × String))) := do
  let fail (cls msg : String) : IO (Except (String × String) (Array (Expr × String))) :=
    pure (.error (cls, msg))
  -- SHAPE. The conclusion has as many leading binders as the recorded statement, so k is the
  -- number of leading binders of the theorem's type beyond those.
  let n := leadingForalls thm.type
  let m := leadingForalls recorded
  if n < m + 2 || n > m + 4 then
    return ← fail "reduce-shape" s!"{mod} must have the type T1 → ... → Tk → S with 2 ≤ k ≤ 4 children before the recorded statement S; it has {if n ≥ m then toString (n - m) else "fewer than 0"} leading binders beyond the {m} of S"
  let k := n - m
  let mut rest := thm.type
  let mut kids : Array Expr := #[]
  for i in [0:k] do
    let .forallE _ t b _ := rest | return ← fail "reduce-shape" "the theorem's type did not peel"
    if b.hasLooseBVar 0 then
      return ← fail "reduce-shape" s!"child {i + 1} of {mod} is a dependent binder: the rest of the type speaks of its proof. Each child must be a plain arrow T → ..."
    kids := kids.push t
    rest := b.lowerLooseBVars 1 1
  -- CONCLUSION: structurally equal to the recorded statement; defeq is not enough.
  unless rest == recorded do
    return ← fail "reduce-conclusion" s!"after its {k} children, {mod} concludes something that is not the recorded statement itself (structural equality; definitional equality is not enough)"
  -- CHILDREN
  for i in [0:k] do
    let t := kids[i]!
    let which := s!"child {i + 1} of {mod}"
    if t.hasLooseBVars then return ← fail "reduce-child" s!"{which} is not closed"
    if t.hasLevelParam || t.hasMVar || t.hasFVar then
      return ← fail "reduce-child" s!"{which} speaks of a universe parameter or a free variable; a child must be a closed proposition"
    let mut sw : Walk := {}
    for c in t.getUsedConstantsAsSet do
      sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
    unless sw.missing.isEmpty do
      return ← fail "reduce-child" s!"{which} rests on declarations outside the pinned library and the definitions root: {sw.missing.toList}. A child may only use what a recorded statement may use"
    let typed ← (runMetaIn stmtEnv do
        let ty ← Meta.whnf (← Meta.inferType t)
        return ty.isProp).toBaseIO
    let isProp ← match typed with
      | .ok b => pure b
      | .error e => return ← fail "reduce-child" s!"{which} could not be typed in the statement environment: {e}"
    unless isProp do return ← fail "reduce-child" s!"{which} is not a proposition"
    if t == mkConst ``False then return ← fail "reduce-child" s!"{which} is False"
    if t == recorded then return ← fail "reduce-child" s!"{which} is the recorded statement itself"
    for j in [0:i] do
      if t == kids[j]! then return ← fail "reduce-child" s!"children {j + 1} and {i + 1} of {mod} are the same proposition"
    -- TEXT cannot travel as a child: no string literal (string and name literals elaborate to
    -- terms with one; a character literal to `Char.ofNat`), no text type among its constants or
    -- their types.
    if (t.find? fun s => s matches .lit (.strVal _)).isSome then
      return ← fail "reduce-child" s!"{which} contains a string or name literal; text cannot travel as a child"
    if let some (c, d) := textConstant stmtEnv t then
      return ← fail "reduce-child" s!"{which} mentions {c}{if c == d then "" else s!", whose type speaks of {d}"}; a child may not speak of the text types {textTypes}"
    -- META: no constant of Lean's own meta types (Lean.*, Std.Format, IO, ...) under the child.
    if let some (c, d) := metaConstant stmtEnv t then
      return ← fail "reduce-child" s!"{which} rests on {d}{if c == d then "" else s!" (through {c})"}, of the meta namespaces {metaRoots}; meta types carry text and code, so a child may not use them"
    -- MDATA: Lean's metadata nodes (`no_index`, ...) carry key-value data, strings included, that
    -- printing drops; a child is a bare term.
    if (t.find? fun s => s matches .mdata ..).isSome then
      return ← fail "reduce-child" s!"{which} carries a metadata (mdata) node, for instance from `no_index`; metadata can carry text and is not printed, so a child is a bare term"
    -- WASTE: a child that holds the statement itself, or that is decidably false.
    if (t.find? (· == recorded)).isSome then
      return ← fail "reduce-waste" s!"{which} contains the recorded statement as a subterm; a child must be a new step, not the statement dressed up"
    if ← decidesFalse stmtEnv t then
      return ← fail "reduce-waste" s!"{which} is decidable and `decide` evaluates it to false (kernel-confirmed); a false child can never be closed"
  -- EXTRA: the module declares the theorem and nothing else.
  let some idx := full.header.moduleNames.idxOf? mod
    | return ← fail "reduce-extra" s!"{mod} is not among the imported modules"
  let mut extra : Array Name := #[]
  for c in full.header.moduleData[idx]!.constants do
    unless c.name == mod || generatedFor full mod c do extra := extra.push c.name
  unless extra.isEmpty do
    return ← fail "reduce-extra" s!"{mod} declares more than its theorem: {extra.toList}. A reduction file holds the one theorem and nothing else"
  -- PRINT, then read back: the text the desk posts must mean exactly the child.
  let mut out : Array (Expr × String) := #[]
  for i in [0:k] do
    let t := kids[i]!
    let which := s!"child {i + 1} of {mod}"
    let printed ← (runMetaIn stmtEnv do
        let f ← Meta.ppExpr (canonBinders t)
        return (f.pretty 1000000).replace "\n" " ").toBaseIO
    let text ← match printed with
      | .ok s => pure s
      | .error e => return ← fail "reduce-child" s!"{which} could not be printed: {e}"
    if text.length > maxChildChars then
      return ← fail "reduce-child" s!"{which} prints as {text.length} characters; a child prints in at most {maxChildChars}"
    match Parser.runParserCategory stmtEnv `term text "<child>" with
    | .error e => return ← fail "reduce-child" s!"{which} prints as `{text}`, which is not one Lean term: {e}"
    | .ok _ => pure ()
    let src := "set_option autoImplicit false\ntheorem PEqualNPChecker.child :\n(\n" ++ text ++ "\n) := sorry\n"
    let (env', msgs) ← Elab.process src stmtEnv {} (fileName := "<child>")
    if msgs.hasErrors then
      return ← fail "reduce-child" s!"{which} prints as `{text}`, which does not elaborate again in the statement environment"
    let some back := env'.find? `PEqualNPChecker.child
      | return ← fail "reduce-child" s!"{which} prints as `{text}`, which did not elaborate to a declaration"
    unless back.levelParams.isEmpty && back.type == t do
      return ← fail "reduce-child" s!"{which} prints as `{text}`, which elaborates again to a different term; the printed text would not mean the child"
    out := out.push (t, text)
  return .ok out

unsafe def run (modStr stmtPath kind : String) : IO UInt32 := do
  let mod := modStr.toName
  unless kind == "check" || kind == "refute" || kind == "reduce" do
    IO.eprintln s!"kind must be check, refute or reduce, got {kind}"; return 3
  initSearchPath (← findSysroot)
  let stmt ← IO.FS.readFile stmtPath

  -- The statement environment: the whole pinned library and the definitions root, and nothing
  -- else of this project. The kernel environment the proof is checked in is built ON it, so a
  -- name means one thing for the statement and for the proof.
  enableInitializersExecution
  let stmtEnv ← importModules #[{ module := statementLibrary }, { module := defsRoot }] {}
    (trustLevel := 0) (loadExts := true)
  let stmtModules := stmtEnv.header.moduleNames
  let mut defsConsts : Std.HashMap Name ConstantInfo := {}
  let mut defsBaseImports : Array Import := #[{ module := `Init }]
  let mut defsModules : Array Name := #[]
  for i in [0:stmtModules.size] do
    let m := stmtModules[i]!
    if isProject m then
      unless isDefs m do
        return ← reject "defs-root" s!"the statement environment reached {m}, which is outside the definitions root"
      defsModules := defsModules.push m
      let d := stmtEnv.header.moduleData[i]!
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return ← reject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker"
        defsConsts := defsConsts.insert c.name c
      for imp in d.imports do
        if isProject imp.module then
          unless isDefs imp.module do
            return ← reject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself"
        else unless defsBaseImports.any (·.module == imp.module) do
          defsBaseImports := defsBaseImports.push { module := imp.module }

  -- The compiled lemma module and every project module under it.
  let full ← importModules #[{ module := mod }] {} (trustLevel := 0)
  let names := full.header.moduleNames
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut projectModules : Array Name := #[]
  let libEnv := stmtEnv.toKernelEnv
  for i in [0:names.size] do
    let m := names[i]!
    if isProject m && !stmtModules.contains m then
      let d := full.header.moduleData[i]!
      projectModules := projectModules.push m
      if isDefs m then
        defsModules := defsModules.push m
        for imp in d.imports do
          if isProject imp.module && !isDefs imp.module then
            return ← reject "defs-root" s!"{m}, in the definitions root, imports {imp.module}, which is outside it. The definitions root may import only the pinned library and itself"
      for c in d.constants do
        if reserved.isPrefixOf c.name then
          return ← reject "reserved-name" s!"{m} declares {c.name}; names under {reserved} belong to the checker"
        -- A name of the pinned library or of the definitions root is theirs alone, whether or
        -- not the declaring file imports the module that holds it. A second copy of one of
        -- their theorems (`sameTheorem`) is left out of what is checked: the name stays theirs.
        if let some l := libEnv.find? c.name then
          if sameTheorem c l then continue
          return ← reject "redeclares" s!"{m} declares {c.name}, a name the pinned library or the definitions root already declares. A project module may not declare it again"
        consts := consts.insert c.name c
  unless names.contains mod && isProject mod do
    return ← reject "not-a-project-module" s!"{mod} is not under one of the project's libraries"

  -- 1. KERNEL: every project constant goes to the kernel again. The definitions root on top of
  -- the pinned modules it imports, alone; everything else on top of the statement environment,
  -- where a name that is already declared cannot be declared a second time.
  let defsBase ← importModules defsBaseImports {} (trustLevel := 0)
  try
    discard <| defsBase.toKernelEnv.replay defsConsts
  catch e =>
    return ← reject "kernel" s!"the kernel refused a declaration of the definitions root: {e}"
  let kenv ← try
      libEnv.replay consts
    catch e =>
      return ← reject "kernel" s!"the kernel refused a declaration under {mod}: {e}"
  -- What the walks below may rest on: a pinned constant, or a project constant the kernel has
  -- just accepted (the replay passes over unsafe and partial ones, so they do not count).
  let checked (n : Name) : Option ConstantInfo := do
    let ci ← kenv.find? n
    match stmtEnv.getModuleIdxFor? n with
    | some idx =>
      if isProject stmtModules[idx.toNat]! then
        let c ← defsConsts[n]?
        if c.isUnsafe || c.isPartial then none else some ci
      else some ci
    | none => if ci.isUnsafe || ci.isPartial then none else some ci

  -- 2. THEOREM
  let some ci := checked mod
    | return ← reject "no-theorem" s!"the file declares no theorem named {mod} (one lemma, one file: the theorem carries the module's name)"
  let .thmInfo thm := ci
    | return ← reject "no-theorem" s!"{mod} is not a theorem"

  -- 3. AXIOMS
  let (_, w) := (walk checked mod).run {}
  unless w.missing.isEmpty do
    return ← reject "kernel" s!"{mod} rests on constants the kernel never accepted: {w.missing.toList}"
  if w.axioms.contains ``sorryAx then
    return ← reject "sorry" s!"{mod} rests on sorry (read from the compiled proof)"
  let extra := w.axioms.filter (!allowedAxioms.contains ·)
  unless extra.isEmpty do
    return ← reject "axiom" s!"{mod} rests on axioms outside the allowlist: {extra.toList}"

  -- 4. STATEMENT: elaborated against the pinned library and the definitions root, and nothing
  -- else of this project.
  match Parser.runParserCategory stmtEnv `term stmt "<recorded statement>" with
  | .error e => return ← reject "statement" s!"the recorded statement is not one Lean term: {e}"
  | .ok _ => pure ()
  let src := "set_option autoImplicit false\ntheorem PEqualNPChecker.recorded :\n(\n" ++ stmt ++ "\n) := sorry\n"
  let (stmtEnv', msgs) ← Elab.process src stmtEnv {} (fileName := "<recorded statement>")
  if msgs.hasErrors then
    for m in msgs.toList do
      if m.severity matches .error then IO.println (← m.toString)
    return ← reject "statement" s!"the recorded statement does not elaborate. A statement may only use the pinned library and the definitions root ({defsRoot}); nothing declared in a lemma file or a helper module exists for it"
  let some rec := stmtEnv'.find? `PEqualNPChecker.recorded
    | return ← reject "statement" "the recorded statement did not produce a declaration"
  -- Every constant the recorded statement speaks of, however deep, is one the statement
  -- environment held before the statement was read, and one the kernel has accepted: the
  -- kernel environment extends that environment, so it is the same constant there.
  let mut sw : Walk := {}
  for c in rec.type.getUsedConstantsAsSet do
    sw := ((walk (fun n => if (libEnv.find? n).isSome then checked n else none) c).run sw).2
  unless sw.missing.isEmpty do
    return ← reject "statement" s!"the recorded statement rests on declarations that are not in the pinned library or the definitions root as the kernel accepted them: {sw.missing.toList}. Write it as one term that needs no auxiliary declaration"
  unless rec.levelParams.length == thm.levelParams.length do
    return ← reject "statement" s!"universe parameters differ: recorded {rec.levelParams}, proved {thm.levelParams}"
  let us := thm.levelParams.map mkLevelParam
  let recorded := rec.type.instantiateLevelParams rec.levelParams us
  let mut goal := if kind == "refute" then mkApp (mkConst ``Not) recorded else recorded
  let mut children : Array (Expr × String) := #[]
  if kind == "reduce" then
    match ← reduceShape stmtEnv full libEnv checked mod thm recorded with
    | .error (cls, msg) => return ← reject cls msg
    | .ok cs =>
      children := cs
      goal := cs.foldr (fun (t, _) b => mkForall `h .default t b) recorded
  let witness := Declaration.thmDecl {
    name := `PEqualNPChecker.witness, levelParams := thm.levelParams, type := goal, value := mkConst mod us }
  match kenv.addDeclCore 0 0 witness (cancelTk? := none) with
  | .ok _ => pure ()
  | .error ex =>
    let what := if kind == "refute" then "the negation of the recorded statement" else "the recorded statement"
    let why ← try (ex.toMessageData {}).toString catch _ => pure "(the kernel's message could not be printed)"
    IO.println s!"kernel: {why}"
    return ← reject "statement" s!"{mod} is not a proof of {what}. It proves: {thm.type}"

  -- The count first, as one fixed line the workflow compares with the CHILD lines it receives, so
  -- a forged extra child line (even numbered next in order) makes the two disagree (red team).
  if kind == "reduce" then IO.println s!"CHILDREN {children.size}"
  for h : i in [0:children.size] do
    IO.println s!"CHILD {i + 1} {children[i].2}"
  IO.println s!"MODULES {" ".intercalate (projectModules.filter (!isDefs ·) |>.toList.map toString)}"
  IO.println s!"DEFS {" ".intercalate (defsModules.toList.map toString)}"
  IO.println s!"ACCEPTED ({kind}): {mod}; axioms {w.axioms.toList}; kernel re-checked {consts.size + defsConsts.size} constants of {(defsModules ++ projectModules.filter (!isDefs ·)).toList}"
  return 0

end PEqualNPChecker

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [mod, stmt, kind] =>
    try PEqualNPChecker.run mod stmt kind
    catch e => IO.eprintln s!"checker fault: {e}"; return 3
  | _ => IO.eprintln "usage: CheckLemma <module> <statement file> <check|refute|reduce>"; return 3
