/-
LEAN-M2-CC-001 · MathIR v1 exporter + code generator (body).

CI generates `MathIR.lean` = `import Lean` + one import per default-target corpus module + this
file, and elaborates it with `lake env lean MathIR.lean` inside the frozen corpus.
Environment:
  MATHIR_OUT   output directory

Fragment v1 ("NatPrimRec"): a computable, safe, non-auxiliary `def f : ℕ → … → ℕ` (1–3 explicit
ℕ arguments) whose definition, read from Lean's *equation lemmas* (`getEqnsFor?`), is either
  * non-recursive:   f x₁ … xₖ = e
  * primitive-recursive on one argument xⱼ:
        f … 0 …       = base(x)
        f … (m+1) …   = step(x, m, f … m …)      (all other arguments passed through unchanged)
where e / base / step are built only from: ℕ numerals, arguments, `+ * - / % ^` on ℕ,
`if a < b / a ≤ b / a = b / a > b / a ≥ b then … else …`, and calls to other functions that are
themselves translated. Anything else is BLOCKED with a recorded reason — never approximated.

Machine semantics (C and Modula-2): 64-bit unsigned, every operation checked. Status OK carries the
exact Lean value; status OVERFLOW means "not representable along this evaluation" and carries no
value. Lean's ℕ edge cases are reproduced: truncated `-`, `x / 0 = 0`, `x % 0 = x`.

Outputs (all deterministic): mathir.json (schema mathir/1), blocked.json, lm2_gen.h, lm2_gen.c,
LM2Gen.def, LM2Gen.mod, lm2_gen_bind.def, lm2_gen_cases.c, report.txt.
-/

open Lean Meta

namespace LeanM2.MathIR

/-! ## IR -/

inductive E where
  | lit  (n : Nat)
  | arg  (i : Nat)            -- i-th function argument
  | idx                       -- the recursion counter m (step only)
  | acc                       -- f … m … (step only)
  | bin  (op : String) (a b : E)                      -- add mul sub div mod pow
  | ite  (cmp : String) (a b : E) (t e : E)          -- lt le eq
  | call (fn : Name) (args : List E)
  deriving Inhabited, BEq

partial def E.json : E → Json
  | .lit n => Json.mkObj [("lit", Lean.toJson (toString n))]
  | .arg i => Json.mkObj [("arg", Lean.toJson i)]
  | .idx => Json.mkObj [("idx", Lean.toJson true)]
  | .acc => Json.mkObj [("acc", Lean.toJson true)]
  | .bin op a b => Json.mkObj [("op", Lean.toJson op), ("a", a.json), ("b", b.json)]
  | .ite c a b t e => Json.mkObj [("if", Lean.toJson c), ("a", a.json), ("b", b.json), ("then", t.json), ("else", e.json)]
  | .call f as => Json.mkObj [("call", Lean.toJson f.toString), ("args", Lean.toJson (as.map E.json))]

partial def E.calls : E → List Name
  | .bin _ a b => a.calls ++ b.calls
  | .ite _ a b t e => a.calls ++ b.calls ++ t.calls ++ e.calls
  | .call f as => f :: as.flatMap E.calls
  | _ => []

inductive FnDef where
  | nonrec (arity : Nat) (body : E)
  | primrec (arity : Nat) (recArg : Nat) (base : E) (step : E)
  deriving Inhabited

def FnDef.arity : FnDef → Nat
  | .nonrec a _ => a
  | .primrec a _ _ _ => a

partial def E.hasPow : E → Bool
  | .bin op a b => op == "pow" || a.hasPow || b.hasPow
  | .ite _ a b t e => a.hasPow || b.hasPow || t.hasPow || e.hasPow
  | .call _ as => as.any E.hasPow
  | _ => false

def FnDef.hasPow : FnDef → Bool
  | .nonrec _ e => e.hasPow
  | .primrec _ _ b s => b.hasPow || s.hasPow

def FnDef.calls : FnDef → List Name
  | .nonrec _ b => b.calls
  | .primrec _ _ b s => b.calls ++ s.calls

/-! ## Reading Lean expressions -/

def isNatTy (e : Expr) : Bool := e.isConstOf ``Nat

/-- ℕ numeral: raw literal, `OfNat.ofNat ℕ n _`, or `Nat.zero`. -/
def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isConstOf ``Nat.zero then some 0
    else match e.getAppFnArgs with
      | (``OfNat.ofNat, #[ty, n, _]) => if isNatTy ty then (match n.consumeMData with | .lit (.natVal k) => some k | _ => none) else none
      | _ => none

def binOps : List (Name × Name × String) :=
  [(``HAdd.hAdd, ``Nat.add, "add"), (``HMul.hMul, ``Nat.mul, "mul"), (``HSub.hSub, ``Nat.sub, "sub"),
   (``HDiv.hDiv, ``Nat.div, "div"), (``HMod.hMod, ``Nat.mod, "mod"), (``HPow.hPow, ``Nat.pow, "pow")]

/-- `(op, a, b)` if `e` is a binary ℕ operation (heterogeneous-class form with all types ℕ, or `Nat.op`). -/
def binOp? (e : Expr) : Option (String × Expr × Expr) :=
  let (fn, args) := e.consumeMData.getAppFnArgs
  binOps.findSome? fun (cls, prim, op) =>
    if fn == cls && args.size == 6 && isNatTy args[0]! && isNatTy args[1]! && isNatTy args[2]! then
      some (op, args[4]!, args[5]!)
    else if fn == prim && args.size == 2 then some (op, args[0]!, args[1]!)
    else none

/-- Comparison `(cmp, a, b)` on ℕ, normalised to lt / le / eq. -/
def cmp? (c : Expr) : Option (String × Expr × Expr) :=
  match c.consumeMData.getAppFnArgs with
  | (``LT.lt, #[ty, _, a, b]) => if isNatTy ty then some ("lt", a, b) else none
  | (``LE.le, #[ty, _, a, b]) => if isNatTy ty then some ("le", a, b) else none
  | (``GT.gt, #[ty, _, a, b]) => if isNatTy ty then some ("lt", b, a) else none
  | (``GE.ge, #[ty, _, a, b]) => if isNatTy ty then some ("le", b, a) else none
  | (``Eq, #[ty, a, b])       => if isNatTy ty then some ("eq", a, b) else none
  | _ => none

/-- Context for translating one right-hand side. -/
structure Ctx where
  self   : Name
  args   : Array Expr        -- fvars standing for the function's arguments (by position)
  idx?   : Option Expr       -- the recursion counter m (step only)
  recArg : Option Nat        -- which argument is the recursion argument

/-- Translate an expression; `Except` carries the blocking reason. -/
partial def tr (c : Ctx) (e : Expr) : MetaM (Except String E) := do
  let e := e.consumeMData
  if let some n := natLit? e then return .ok (.lit n)
  if e.isFVar then
    -- the recursion counter m must be recognised BEFORE argument lookup: in the step equation
    -- args[j] is m itself, and `m` means the loop counter i, not the original argument aⱼ = n.
    if c.idx? == some e then return .ok .idx
    if let some i := c.args.findIdx? (· == e) then return .ok (.arg i)
    return .error "free variable not an argument"
  if let some (op, a, b) := binOp? e then
    match ← tr c a, ← tr c b with
    | .ok a', .ok b' => return .ok (.bin op a' b')
    | .error r, _ | _, .error r => return .error r
  -- Nat.succ x  ==  x + 1
  if e.isAppOfArity ``Nat.succ 1 then
    match ← tr c e.appArg! with
    | .ok a => return .ok (.bin "add" a (.lit 1))
    | .error r => return .error r
  -- if-then-else on a ℕ comparison
  if e.isAppOfArity ``ite 5 then
    let args := e.getAppArgs
    unless isNatTy args[0]! do return .error "ite at a non-ℕ type"
    let some (k, a, b) := cmp? args[1]! | return .error s!"ite condition not a ℕ comparison"
    match ← tr c a, ← tr c b, ← tr c args[3]!, ← tr c args[4]! with
    | .ok a', .ok b', .ok t', .ok f' => return .ok (.ite k a' b' t' f')
    | .error r, _, _, _ | _, .error r, _, _ | _, _, .error r, _ | _, _, _, .error r => return .error r
  let (fn, fargs) := e.getAppFnArgs
  if fn == c.self then
    -- must be the recursive call f … m … with every other argument passed through unchanged
    let some j := c.recArg | return .error "recursion in a non-recursive equation"
    let some m := c.idx? | return .error "recursive call outside the step equation"
    if fargs.size != c.args.size then return .error "partial recursive call"
    for h : i in [0:fargs.size] do
      let want := if i == j then m else c.args[i]!
      unless fargs[i] == want do return .error "non-primitive recursion (arguments change)"
    return .ok .acc
  if fn != .anonymous && fargs.all (fun _ => true) then
    -- a call to another function: translated later only if that function is itself translated
    let ci ← getConstInfo fn
    let ty := ci.type
    let isNatFn ← forallTelescope ty fun xs body => do
      if !isNatTy body then return false
      for x in xs do
        unless isNatTy (← inferType x) do return false
      return xs.size == fargs.size && xs.size ≥ 1
    unless isNatFn do return .error s!"unsupported: {fn}"
    let mut out : List E := []
    for a in fargs do
      match ← tr c a with
      | .ok a' => out := out ++ [a']
      | .error r => return .error r
    return .ok (.call fn out)
  return .error s!"unsupported expression ({e.ctorName})"

/-- Arity if `ty` is `ℕ → … → ℕ` with 1–3 explicit ℕ binders. -/
def natArity? (ty : Expr) : MetaM (Option Nat) :=
  forallTelescope ty fun xs body => do
    if !isNatTy body || xs.isEmpty || xs.size > 3 then return none
    for x in xs do
      unless isNatTy (← inferType x) do return none
      unless (← x.fvarId!.getBinderInfo).isExplicit do return none
    return some xs.size

/-- Read the definition from its equation lemmas (or, if it has none, its body). -/
def extract (n : Name) (arity : Nat) : MetaM (Except String FnDef) := do
  let eqns? ← try getEqnsFor? n catch _ => pure none
  match eqns? with
  | none | some #[] =>
    -- non-recursive: unfold the body
    let ci ← getConstInfo n
    let some v := ci.value? | return .error "no definition body"
    lambdaTelescope v fun xs body => do
      if xs.size != arity then return .error "body arity differs from type arity"
      match ← tr { self := n, args := xs, idx? := none, recArg := none } body with
      | .ok e => return .ok (.nonrec arity e)
      | .error r => return .error r
  | some eqns =>
    if eqns.size == 1 then
      let thm ← getConstInfo eqns[0]!
      forallTelescope thm.type fun _ eq => do
        let some (_, lhs, rhs) := eq.eq? | return .error "equation is not an Eq"
        let largs := lhs.getAppArgs
        unless largs.all (·.isFVar) && largs.size == arity do return .error "pattern-matching single equation"
        match ← tr { self := n, args := largs, idx? := none, recArg := none } rhs with
        | .ok e => return .ok (.nonrec arity e)
        | .error r => return .error r
    else if eqns.size == 2 then
      -- expect: one equation with argument j = 0, one with argument j = m + 1
      let mut base? : Option E := none
      let mut step? : Option E := none
      let mut rec? : Option Nat := none
      for eqn in eqns do
        let thm ← getConstInfo eqn
        let r ← forallTelescope thm.type fun _ eq => do
          let some (_, lhs, rhs) := eq.eq? | return Except.error "equation is not an Eq"
          let largs := lhs.getAppArgs
          if largs.size != arity then return .error "partial application in equation"
          let nonVar := (List.range arity).filter (fun i => !largs[i]!.isFVar)
          match nonVar with
          | [j] =>
            let pat := largs[j]!
            if natLit? pat == some 0 then
              let args := largs.set! j (mkNatLit 0)
              match ← tr { self := n, args := args, idx? := none, recArg := some j } rhs with
              | .ok e => return .ok (j, true, e)
              | .error r => return .error r
            else
              let m? : Option Expr :=
                match binOp? pat with
                | some ("add", m, one) => if natLit? one == some 1 && m.isFVar then some m else none
                | _ => if pat.isAppOfArity ``Nat.succ 1 && pat.appArg!.isFVar then some pat.appArg! else none
              let some m := m? | return .error "recursion pattern is not 0 / m+1"
              let args := largs.set! j m
              match ← tr { self := n, args := args, idx? := some m, recArg := some j } rhs with
              | .ok e => return .ok (j, false, e)
              | .error r => return .error r
          | _ => return .error "not recursion on exactly one argument"
        match r with
        | .error e => return .error e
        | .ok (j, isBase, e) =>
          if rec? != none && rec? != some j then return .error "equations recurse on different arguments"
          rec? := some j
          if isBase then base? := some e else step? := some e
      match base?, step?, rec? with
      | some b, some s, some j => return .ok (.primrec arity j b s)
      | _, _, _ => return .error "missing base or step equation"
    else
      return .error s!"{eqns.size} equations (only non-recursive or 0/m+1 primitive recursion supported)"

/-! ## Names -/

def sanitize (s : String) : String :=
  let cs := s.toList.map fun c => if c.isAlphanum && c.toNat < 128 then c else '_'
  String.mk cs

/-! ## C emission -/

structure CG where
  lines : Array String := #[]
  tmp   : Nat := 0

abbrev CGM := StateM CG

def emitC (l : String) : CGM Unit := modify fun s => { s with lines := s.lines.push l }
def freshC : CGM String := modifyGet fun s => (s!"t{s.tmp}", { s with tmp := s.tmp + 1 })

/-- Emit C statements computing `e`; returns the C expression (a variable or literal). -/
partial def cExpr (sym : Name → String) (ind : String) : E → CGM String
  | .lit n => pure s!"{n}ULL"
  | .arg i => pure s!"a{i}"
  | .idx => pure "i"
  | .acc => pure "acc"
  | .bin op a b => do
    let x ← cExpr sym ind a
    let y ← cExpr sym ind b
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if (lm2_{op}({x}, {y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .ite k a b th el => do
    let x ← cExpr sym ind a
    let y ← cExpr sym ind b
    let t ← freshC
    let cond := match k with | "lt" => s!"{x} < {y}" | "le" => s!"{x} <= {y}" | _ => s!"{x} == {y}"
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if ({cond}) \{"
    let r1 ← cExpr sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExpr sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← cExpr sym ind a)
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if ({sym f}({", ".intercalate (vs.toList ++ [s!"&{t}"])}) != LM2_OK) return LM2_OVERFLOW;"
    return t

def cParams (arity : Nat) : String :=
  ", ".intercalate ((List.range arity).map (s!"uint64_t a{·}") ++ ["uint64_t *out"])

def cFunction (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : CGM Unit := do
    emitC "  if (out == 0) return LM2_ERR_NULL;"
    match d with
    | .nonrec _ e =>
      let r ← cExpr sym "  " e
      emitC s!"  *out = {r};"
    | .primrec _ j b s =>
      emitC "  uint64_t acc, i;"
      let rb ← cExpr sym "  " b
      emitC s!"  acc = {rb};"
      emitC s!"  for (i = 0ULL; i < a{j}; i++) \{"
      let rs ← cExpr sym "    " s
      emitC s!"    acc = {rs};"
      emitC "  }"
      emitC "  *out = acc;"
    emitC "  return LM2_OK;"
  let st := (body.run {}).2
  s!"/* Lean: {n} */\nint32_t {sym n}({cParams d.arity}) \{\n" ++ "\n".intercalate st.lines.toList ++ "\n}\n"

/-! ## Modula-2 emission (native; uses LM2Nat for checked operations) -/

structure MG where
  lines : Array String := #[]
  vars  : Array String := #[]
  tmp   : Nat := 0

abbrev MGM := StateM MG

def emitM (l : String) : MGM Unit := modify fun s => { s with lines := s.lines.push l }
def freshM : MGM String := modifyGet fun s => (s!"t{s.tmp}", { s with tmp := s.tmp + 1, vars := s.vars.push s!"t{s.tmp}" })

def m2Op : String → String
  | "add" => "Add" | "mul" => "Mul" | "sub" => "Sub" | "div" => "Div" | "mod" => "Mod" | _ => "Pow"

partial def mExpr (sym : Name → String) (ind : String) : E → MGM String
  | .lit n => pure (toString n)
  | .arg i => pure s!"a{i}"
  | .idx => pure "i"
  | .acc => pure "acc"
  | .bin op a b => do
    let x ← mExpr sym ind a
    let y ← mExpr sym ind b
    let t ← freshM
    emitM s!"{ind}IF LM2Nat.{m2Op op}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .ite k a b th el => do
    let x ← mExpr sym ind a
    let y ← mExpr sym ind b
    let t ← freshM
    let cond := match k with | "lt" => s!"{x} < {y}" | "le" => s!"{x} <= {y}" | _ => s!"{x} = {y}"
    emitM s!"{ind}IF {cond} THEN"
    let r1 ← mExpr sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExpr sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← mExpr sym ind a)
    let t ← freshM
    emitM s!"{ind}IF {sym f}({", ".intercalate (vs.toList ++ [t])}) # Ok THEN RETURN Overflow END;"
    return t

def mParams (arity : Nat) : String :=
  let as := ", ".intercalate ((List.range arity).map (s!"a{·}"))
  s!"{as}: LONGCARD; VAR out: LONGCARD"

def mProcedure (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : MGM Unit := do
    match d with
    | .nonrec _ e =>
      let r ← mExpr sym "  " e
      emitM s!"  out := {r};"
    | .primrec _ j b s =>
      let rb ← mExpr sym "  " b
      emitM s!"  acc := {rb};"
      emitM "  i := 0;"
      emitM s!"  WHILE i < a{j} DO"
      let rs ← mExpr sym "    " s
      emitM s!"    acc := {rs};"
      emitM "    INC(i)"
      emitM "  END;"
      emitM "  out := acc;"
    emitM "  RETURN Ok"
  let st := (body.run {}).2
  let extra := match d with | .primrec .. => #["acc", "i"] | _ => #[]
  let vars := st.vars ++ extra
  let varDecl := if vars.isEmpty then "" else s!"VAR\n  {", ".intercalate vars.toList}: LONGCARD;\n"
  s!"(* Lean: {n} *)\nPROCEDURE {sym n} ({mParams d.arity}) : INTEGER;\n{varDecl}BEGIN\n" ++
    "\n".intercalate st.lines.toList ++ s!"\nEND {sym n};\n"

/-! ## Reference values -/

def u64Max : Nat := 2 ^ 64 - 1

unsafe def evalN (env : Environment) (n : Name) (arity : Nat) (args : List Nat) : Except String Nat := do
  match arity, args with
  | 1, [a] => return (← env.evalConst (Nat → Nat) {} n (checkMeta := false)) a
  | 2, [a, b] => return (← env.evalConst (Nat → Nat → Nat) {} n (checkMeta := false)) a b
  | 3, [a, b, c] => return (← env.evalConst (Nat → Nat → Nat → Nat) {} n (checkMeta := false)) a b c
  | _, _ => throw "arity"

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Test inputs. For functions that recurse or use `^` (directly or through calls) every argument
stays ≤ 200, so the Lean reference evaluation stays cheap; others also get 2^32-1, 2^63, 2^64-1. -/
def inputs (arity : Nat) (bounded : Bool) (seed : UInt64) : Array (List Nat) := Id.run do
  let small : List Nat := [0, 1, 2, 3, 5, 7, 10, 16, 31, 64]
  let big : List Nat := if bounded then [100, 199] else [2 ^ 32 - 1, 2 ^ 63, 2 ^ 64 - 1]
  let vals := small ++ big
  let mut out : Array (List Nat) := #[]
  match arity with
  | 1 => for a in vals do out := out.push [a]
  | 2 => for a in vals do for b in vals do out := out.push [a, b]
  | _ => for a in small.take 6 ++ big do for b in small.take 6 ++ big do for c in small.take 6 ++ big do out := out.push [a, b, c]
  let mut s := seed
  for _ in List.range 300 do
    let mut xs : List Nat := []
    for _ in List.range arity do
      s := lcg s
      let v := if bounded then (s >>> 56).toNat % 201 else
        if (s &&& 1) == 0 then (s >>> 48).toNat else s.toNat
      xs := xs ++ [v]
    out := out.push xs
  return out

end LeanM2.MathIR

open LeanM2.MathIR in
set_option maxHeartbeats 0 in
#eval show MetaM Unit from do
  let env ← getEnv
  let some outDir ← IO.getEnv "MATHIR_OUT" | throwError "MATHIR_OUT is not set"
  let some modsPath ← IO.getEnv "MATHIR_MODS" | throwError "MATHIR_MODS is not set"
  IO.FS.createDirAll outDir
  let out (f : String) : System.FilePath := System.FilePath.mk outDir / f
  -- corpus modules (TSV: rendered name, then components)
  let wanted := (← IO.FS.lines modsPath).filter (· ≠ "") |>.map fun l =>
    ((l.splitOn "\t").drop 1).foldl Name.mkStr .anonymous
  -- 1. candidates: computable, safe, non-auxiliary ℕ^k → ℕ defs (k ≤ 3) in corpus modules
  let mut cands : Array (Name × Nat) := #[]
  for m in wanted do
    let some idx := env.header.moduleNames.findIdx? (· == m) | continue
    for ci in env.header.moduleData[idx]!.constants do
      let .defnInfo dv := ci | continue
      unless dv.safety == .safe do continue
      if isNoncomputable env ci.name || ci.name.isInternal then continue
      if (Compiler.getImplementedBy? env ci.name).isSome || isExtern env ci.name then continue
      if let some k ← natArity? ci.type then cands := cands.push (ci.name, k)
  cands := cands.qsort (fun a b => a.1.toString < b.1.toString)
  -- 2. extract
  let mut defs : Std.HashMap Name FnDef := {}
  let mut blocked : Array (Name × String) := #[]
  for (n, k) in cands do
    match ← (try extract n k catch e => do pure (.error s!"exception: {← e.toMessageData.toString}")) with
    | .ok d => defs := defs.insert n d
    | .error r => blocked := blocked.push (n, r)
  -- 3. closure: a def is translatable only if every callee is translatable
  let mut changed := true
  while changed do
    changed := false
    for (n, d) in defs.toList do
      if let some bad := d.calls.find? (fun c => !defs.contains c) then
        defs := defs.erase n
        blocked := blocked.push (n, s!"calls untranslated function {bad}")
        changed := true
  -- 4. deterministic order: dependencies first, then by name
  let names := (defs.toList.map (·.1)).toArray.qsort (fun a b => a.toString < b.toString)
  let mut order : Array Name := #[]
  let mut placed : Std.HashSet Name := {}
  while order.size < names.size do
    let before := order.size
    for n in names do
      if !placed.contains n && (defs.get! n).calls.all placed.contains then
        order := order.push n; placed := placed.insert n
    if order.size == before then throwError "call cycle among translated functions"
  -- symbols: sanitized names, collisions disambiguated by order index
  let mut symOf : Std.HashMap Name String := {}
  let mut used : Std.HashSet String := {}
  for n in order do
    let base := sanitize n.toString
    let s := if used.contains base then base ++ "_" ++ toString used.size else base
    used := used.insert s; symOf := symOf.insert n s
  let mut idxOf : Std.HashMap Name Nat := {}
  for h : k in [0:order.size] do idxOf := idxOf.insert order[k] k
  let cSym (n : Name) : String := "lm2_" ++ symOf.get! n
  let mSym (n : Name) : String := "F_" ++ symOf.get! n
  -- 5. C
  let hdr := "/* Generated by lean-m2/tools/mathir_body.lean (MathIR v1). Do not edit. */\n#ifndef LM2_GEN_H\n#define LM2_GEN_H\n#include <stdint.h>\n#define LM2_OK 0\n#define LM2_OVERFLOW 1\n#define LM2_ERR_NULL (-1)\n" ++
    String.join (order.toList.map fun n => s!"int32_t {cSym n}({cParams (defs.get! n).arity});\n#define LM2_FN_{symOf.get! n} {idxOf.get! n}u\n") ++
    "int32_t lm2_gen_call(uint32_t fn, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t *out);\nuint32_t lm2_gen_count(void);\n#endif\n"
  let cBody := "/* Generated by lean-m2/tools/mathir_body.lean (MathIR v1). Do not edit.\n   Compiled only by CompCert. Every operation is checked (lm2_nat.h). */\n#include \"lm2_nat.h\"\n#include \"lm2_gen.h\"\n\n" ++
    String.join (order.toList.map fun n => cFunction cSym n (defs.get! n) ++ "\n") ++
    "int32_t lm2_gen_call(uint32_t fn, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t *out) {\n  (void)a0; (void)a1; (void)a2;\n  switch (fn) {\n" ++
    String.join (order.toList.mapIdx fun i n =>
      let d := defs.get! n
      let as := (List.range d.arity).map (s!"a{·}")
      s!"  case {i}u: return {cSym n}({", ".intercalate (as ++ ["out"])});\n") ++
    "  default: return LM2_ERR_NULL;\n  }\n}\n" ++ s!"uint32_t lm2_gen_count(void) \{ return {order.size}u; }\n"
  IO.FS.writeFile (out "lm2_gen.h") hdr
  IO.FS.writeFile (out "lm2_gen.c") cBody
  -- 6. Modula-2 (native) + binding to the C dispatcher
  let mDef := "DEFINITION MODULE LM2Gen;\n(* Generated by lean-m2/tools/mathir_body.lean (MathIR v1). Do not edit.\n   Native Modula-2: NOT a wrapper around the C code. *)\nCONST\n  Ok = 0;\n  Overflow = 1;\n" ++
    String.join (order.toList.mapIdx fun i n => s!"  Fn{symOf.get! n} = {i};\n") ++
    String.join (order.toList.map fun n => s!"PROCEDURE {mSym n} ({mParams (defs.get! n).arity}) : INTEGER;\n") ++
    "PROCEDURE Call (fn: CARDINAL; a0, a1, a2: LONGCARD; VAR out: LONGCARD) : INTEGER;\nEND LM2Gen.\n"
  let mMod := "IMPLEMENTATION MODULE LM2Gen;\n(* Generated by lean-m2/tools/mathir_body.lean (MathIR v1). Do not edit. *)\nIMPORT LM2Nat;\n\n" ++
    String.join (order.toList.map fun n => mProcedure mSym n (defs.get! n) ++ "\n") ++
    "PROCEDURE Call (fn: CARDINAL; a0, a1, a2: LONGCARD; VAR out: LONGCARD) : INTEGER;\nBEGIN\n  CASE fn OF\n" ++
    String.join (order.toList.mapIdx fun i n =>
      let d := defs.get! n
      let as := (List.range d.arity).map (s!"a{·}")
      s!"  | {i}: RETURN {mSym n}({", ".intercalate (as ++ ["out"])})\n") ++
    "  ELSE RETURN -1\n  END\nEND Call;\n\nEND LM2Gen.\n"
  IO.FS.writeFile (out "LM2Gen.def") mDef
  IO.FS.writeFile (out "LM2Gen.mod") mMod
  IO.FS.writeFile (out "lm2_gen_bind.def")
    "DEFINITION MODULE FOR \"C\" lm2_gen_bind;\n(* Generated. Binding to the CompCert-compiled dispatcher in lm2_gen.c. *)\nFROM SYSTEM IMPORT ADDRESS;\nEXPORT UNQUALIFIED lm2_gen_call, lm2_gen_count;\nPROCEDURE lm2_gen_call (fn: CARDINAL; a0, a1, a2: LONGCARD; out: ADDRESS) : INTEGER;\nPROCEDURE lm2_gen_count () : CARDINAL;\nEND lm2_gen_bind.\n"
  -- 7. reference vectors (Lean evaluates the corpus definitions)
  let isRec (n : Name) : Bool := match defs.get! n with | .primrec .. => true | _ => false
  let mut reach : Std.HashMap Name Bool := {}
  for n in order do
    -- bounded inputs for anything that recurses or exponentiates, directly or through calls
    reach := reach.insert n (isRec n || (defs.get! n).hasPow || (defs.get! n).calls.any (reach.getD · false))
  let mut cFn := ""; let mut cA0 := ""; let mut cA1 := ""; let mut cA2 := ""; let mut cSt := ""; let mut cV := ""
  let mut ncases := 0; let mut nok := 0
  let mut evalFail : Array (Name × String) := #[]
  for h : i in [0:order.size] do
    let n := order[i]
    let d := defs.get! n
    for xs in inputs d.arity (reach.getD n false) (0x5EED0000 + i.toUInt64) do
      match unsafe evalN env n d.arity xs with
      | .error e => evalFail := evalFail.push (n, e); break
      | .ok v =>
        let (st, val) := if v ≤ u64Max then (0, v) else (1, 0)
        let pad := xs ++ List.replicate (3 - xs.length) 0
        cFn := cFn ++ s!"{i}u,"; cA0 := cA0 ++ s!"{pad[0]!}ULL,"; cA1 := cA1 ++ s!"{pad[1]!}ULL,"
        cA2 := cA2 ++ s!"{pad[2]!}ULL,"; cSt := cSt ++ s!"{st},"; cV := cV ++ s!"{val}ULL,"
        ncases := ncases + 1
        if st == 0 then nok := nok + 1
  unless evalFail.isEmpty do throwError m!"reference evaluation failed: {evalFail.toList.map (·.1)}"
  IO.FS.writeFile (out "lm2_gen_cases.c") <|
    "/* Generated by mathir_body.lean: Lean-evaluated reference values. Do not edit. */\n#include <stdint.h>\n#include <stddef.h>\n" ++
    s!"#define N {ncases}u\nstatic const uint32_t F[N]=\{{cFn}};\nstatic const uint64_t A0[N]=\{{cA0}};\nstatic const uint64_t A1[N]=\{{cA1}};\nstatic const uint64_t A2[N]=\{{cA2}};\nstatic const int32_t ST[N]=\{{cSt}};\nstatic const uint64_t V[N]=\{{cV}};\n" ++
    "uint32_t lm2_gen_case_count(void) { return N; }\nint32_t lm2_gen_case_get(uint32_t i, uint32_t *f, uint64_t *a0, uint64_t *a1, uint64_t *a2, int32_t *st, uint64_t *v) {\n  if (i >= N || !f || !a0 || !a1 || !a2 || !st || !v) return -1;\n  *f = F[i]; *a0 = A0[i]; *a1 = A1[i]; *a2 = A2[i]; *st = ST[i]; *v = V[i];\n  return 0;\n}\n"
  -- 8. MathIR + reports
  let irJson := Json.mkObj [
    ("schema", toJson "mathir/1"), ("fragment", toJson "NatPrimRec v1"),
    ("lean", toJson Lean.versionString),
    ("functions", toJson (order.toList.mapIdx fun i n =>
      let d := defs.get! n
      Json.mkObj ([("id", toJson i), ("name", toJson n.toString), ("c_symbol", toJson (cSym n)),
        ("m2_symbol", toJson (mSym n)), ("arity", toJson d.arity)] ++
        match d with
        | .nonrec _ e => [("kind", toJson "nonrec"), ("body", e.json)]
        | .primrec _ j b s => [("kind", toJson "primrec"), ("rec_arg", toJson j), ("base", b.json), ("step", s.json)])))]
  IO.FS.writeFile (out "mathir.json") (irJson.pretty ++ "\n")
  let blockedSorted := blocked.qsort (fun a b => a.1.toString < b.1.toString)
  IO.FS.writeFile (out "blocked.json") ((toJson (blockedSorted.map fun (n, r) =>
    Json.mkObj [("name", toJson n.toString), ("reason", toJson r)])).pretty ++ "\n")
  -- reason histogram (first word groups)
  let mut hist : Std.HashMap String Nat := {}
  for (_, r) in blocked do
    let key := if r.startsWith "unsupported: " then "unsupported constant" else if r.startsWith "calls untranslated" then "calls untranslated function" else r
    hist := hist.insert key (hist.getD key 0 + 1)
  let histLines := (hist.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.map fun (k, v) => s!"  {v}  {k}"
  let mut consts : Std.HashMap String Nat := {}
  for (_, r) in blocked do
    if r.startsWith "unsupported: " then
      let k := (r.drop 13).toString
      consts := consts.insert k (consts.getD k 0 + 1)
  let topConsts := ((consts.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 15).map fun (k, v) => s!"  {v}  {k}"
  let report := s!"MATHIR candidates={cands.size} translated={order.size} blocked={blocked.size} cases={ncases} ok={nok} overflow={ncases - nok}\n" ++
    "translated:\n" ++ String.join (order.toList.map fun n => s!"  {n} ({(defs.get! n).arity}-ary{if isRec n then ", primrec" else ""})\n") ++
    "blocked reasons:\n" ++ "\n".intercalate histLines ++ "\ntop unsupported constants:\n" ++ "\n".intercalate topConsts ++ "\n"
  IO.FS.writeFile (out "report.txt") report
  IO.println s!"MATHIR candidates={cands.size} translated={order.size} blocked={blocked.size} cases={ncases} ok={nok} overflow={ncases - nok}"
