/-
LEAN-M2-CC-001 · MathIR v2 exporter + code generator (body).

CI generates `MathIR.lean` = `import Lean` + one import per default-target corpus module + this
file, and elaborates it with `lake env lean MathIR.lean` inside the frozen corpus.
Environment:  MATHIR_OUT (output directory), MATHIR_MODS (TSV of modules: name, components…)

Fragment v2 ("NatLoops"). A computable, safe, non-auxiliary `def f : ℕ → … → ℕ` (1–3 explicit ℕ
arguments) is translated when its definition — read from Lean's *equation lemmas* (`getEqnsFor?`),
or its body if it has none — is either
  * direct:       f x₁ … xₖ = e
  * recursive on one argument xⱼ with K ≥ 1 base cases (lookback recursion):
        f … 0 … = b₀,  …,  f … (K-1) … = b_{K-1},   f … (m+K) … = step(x, m, f … (m+j) … for j < K)
    with every other argument passed through unchanged (K = 1 is primitive recursion),
and e / bᵢ / step are built only from:
  * ℕ numerals, arguments, `let`
  * `+ * - / % ^`, `min`, `max`, `Nat.gcd`, `Nat.lcm`, `Nat.factorial`, `Nat.choose`, `Nat.sqrt`,
    `Nat.minFac`
  * `if p then a else b` where p is a decidable predicate built from `< ≤ = ≠ > ≥`, `∣`,
    `Nat.Prime`, `Even`, `Odd`, `∧ ∨ ¬`, `True`, `False`
  * `∑` / `∏` / `Finset.card` over `Finset.range n`, `Finset.Icc/Ico/Ioc/Ioo a b`, optionally
    `Finset.filter`ed by such a predicate
  * calls to other functions that are themselves translated.
Anything else is BLOCKED with a recorded reason — never approximated.

Machine semantics (C and Modula-2): 64-bit unsigned, every operation checked. Status OK carries the
exact Lean value; OVERFLOW means "not representable along this evaluation" and carries no value.
Lean/Mathlib edge cases are reproduced (truncated `-`, `x/0 = 0`, `x%0 = x`, `0^0 = 1`,
`gcd 0 0 = 0`, `lcm 0 b = 0`, `choose n k = 0` for k > n, `minFac 0 = 2`, `minFac 1 = 1`, `0 ∣ b ↔ b = 0`).

Reference values: inputs are first run through a budgeted interpreter of the IR (exact ℕ, aborts on
size/step budget); within budget, the reference is Lean's compiled corpus definition, and the IR must
agree with it on every input (extraction-fidelity check). Over-budget inputs are skipped and counted.

Outputs: mathir.json (schema mathir/2), blocked.json, lm2_gen.h, lm2_gen.c, LM2Gen.def, LM2Gen.mod,
lm2_gen_bind.def, lm2_gen_cases.c, report.txt.
-/

open Lean Meta

namespace LeanM2.MathIR

/-! ## IR -/

/-- Values and booleans share one IR: boolean nodes evaluate to 0 / 1. -/
inductive E where
  | lit  (n : Nat)
  | arg  (i : Nat)                       -- i-th function argument
  | idx                                  -- recursion counter m (step only)
  | prev (j : Nat)                       -- f … (m + j) …  (step only, j < K)
  | lvar (id : Nat)                      -- loop variable
  | bin  (op : String) (a b : E)         -- add mul sub div mod pow | ℤ: iadd isub imul ipow (exponent ℕ)
  | prim (op : String) (args : List E)   -- min max gcd lcm fact choose sqrt minfac fib log log2 padic
                                         -- bigomega digsum diglen digrev | dvd prime (boolean)
                                         -- ℕ→ℤ: ofnat | ℤ→ℤ: ineg isign | ℤ→ℕ: tonat natabs
                                         -- ℚ (exact path only): ℕ→ℚ qofnat, ℤ→ℚ qofint, qneg qinv,
                                         --   ℚ→ℤ qnum, ℚ→ℕ qden; bin qadd qsub qmul qdiv qpow; fold qsum qprod
  | cmp  (k : String) (a b : E)          -- lt le eq | ℤ operands: ilt ile ieq (boolean)
  | and  (a b : E)
  | or   (a b : E)
  | not  (a : E)
  | ite  (c t e : E)                     -- c is boolean
  | fold (op : String) (id : Nat) (lo hi : E) (incl : Bool) (filt : E) (body : E)  -- sum prod count max | ℤ body: isum iprod
  | call (fn : Name) (args : List E)
  -- left fold over a ℕ range with an accumulator (lists): a := init; for each counter value k
  -- passing filt, a := body (lvar id = k, lvar acc = a). Accumulator ids are ≥ accBase.
  | iter (id acc : Nat) (lo hi : E) (incl : Bool) (filt init body : E)

instance : Inhabited E := ⟨.lit 0⟩

/-- Loop-variable ids at or above this denote fold accumulators (an ℕ value in every backend,
held at full width on the wide path). -/
def accBase : Nat := 1000000

partial def E.json : E → Json
  | .lit n => Json.mkObj [("lit", Lean.toJson (toString n))]
  | .arg i => Json.mkObj [("arg", Lean.toJson i)]
  | .idx => Json.mkObj [("idx", Lean.toJson true)]
  | .prev j => Json.mkObj [("prev", Lean.toJson j)]
  | .lvar i => Json.mkObj [("lvar", Lean.toJson i)]
  | .bin op a b => Json.mkObj [("op", Lean.toJson op), ("a", a.json), ("b", b.json)]
  | .prim op as => Json.mkObj [("prim", Lean.toJson op), ("args", Lean.toJson (as.map E.json))]
  | .cmp k a b => Json.mkObj [("cmp", Lean.toJson k), ("a", a.json), ("b", b.json)]
  | .and a b => Json.mkObj [("and", Lean.toJson [a.json, b.json])]
  | .or a b => Json.mkObj [("or", Lean.toJson [a.json, b.json])]
  | .not a => Json.mkObj [("not", a.json)]
  | .ite c t e => Json.mkObj [("if", c.json), ("then", t.json), ("else", e.json)]
  | .fold op i lo hi incl f b => Json.mkObj [("fold", Lean.toJson op), ("var", Lean.toJson i), ("lo", lo.json),
      ("hi", hi.json), ("inclusive", Lean.toJson incl), ("filter", f.json), ("body", b.json)]
  | .call f as => Json.mkObj [("call", Lean.toJson f.toString), ("args", Lean.toJson (as.map E.json))]
  | .iter i a lo hi incl f init b => Json.mkObj [("iter", Lean.toJson i), ("acc", Lean.toJson a), ("lo", lo.json),
      ("hi", hi.json), ("inclusive", Lean.toJson incl), ("filter", f.json), ("init", init.json), ("body", b.json)]

partial def E.children : E → List E
  | .bin _ a b | .cmp _ a b | .and a b | .or a b => [a, b]
  | .not a => [a]
  | .prim _ as | .call _ as => as
  | .ite c t e => [c, t, e]
  | .fold _ _ lo hi _ f b => [lo, hi, f, b]
  | .iter _ _ lo hi _ f init b => [lo, hi, f, init, b]
  | _ => []

partial def E.calls (e : E) : List Name :=
  (match e with | .call f _ => [f] | _ => []) ++ e.children.flatMap E.calls

/-- Anything whose reference evaluation may be costly: pow, loops, heavy builtins. -/
partial def E.heavy (e : E) : Bool :=
  (match e with
   | .bin "pow" _ _ | .bin "ipow" _ _ | .bin "qpow" _ _ | .fold .. | .iter .. => true
   | .prim op _ => op ∈ ["fact", "choose", "minfac", "prime", "lcm", "fib", "bigomega"]
   | _ => false) || e.children.any E.heavy

inductive FnDef where
  | direct (arity : Nat) (body : E)                                    -- non-recursive
  | recur  (arity : Nat) (recArg : Nat) (bases : List E) (step : E)    -- K = bases.length ≥ 1 (`rec` is the auto-generated recursor)

instance : Inhabited FnDef := ⟨.direct 0 default⟩

def FnDef.arity : FnDef → Nat
  | .direct a _ | .recur a _ _ _ => a

def FnDef.exprs : FnDef → List E
  | .direct _ b => [b]
  | .recur _ _ bs s => bs ++ [s]

def FnDef.calls (d : FnDef) : List Name := d.exprs.flatMap E.calls
def FnDef.heavy (d : FnDef) : Bool := (match d with | .recur .. => true | _ => false) || d.exprs.any E.heavy

/-! ## Reading Lean expressions -/

def isNatTy (e : Expr) : Bool := e.isConstOf ``Nat
def isIntTy (e : Expr) : Bool := e.isConstOf ``Int
def isRatTy (e : Expr) : Bool := e.isConstOf `Rat

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

/-- If `e` is `m + K` (or `Nat.succ` applied K times to `m`) with `m` a free variable: `(m, K)`. -/
partial def offsetPattern? (e : Expr) : Option (Expr × Nat) :=
  let e := e.consumeMData
  if e.isFVar then some (e, 0)
  else if e.isAppOfArity ``Nat.succ 1 then (offsetPattern? e.appArg!).map fun (m, k) => (m, k + 1)
  else match binOp? e with
    | some ("add", x, y) => match natLit? y with
      | some k => (offsetPattern? x).map fun (m, j) => (m, j + k)
      | none => none
    | some ("sub", x, y) => match natLit? y, offsetPattern? x with
      | some k, some (m, j) => if j ≥ k then some (m, j - k) else none
      | _, _ => none
    | _ => none

/-- Context for translating one right-hand side. -/
structure Ctx where
  self   : Name
  args   : Array Expr             -- fvars standing for the function's arguments (by position)
  idx?   : Option Expr            -- the recursion counter m (step only)
  recArg : Option Nat             -- which argument is the recursion argument
  K      : Nat := 0               -- lookback depth (step only)
  loops  : Array (Expr × Nat) := #[]   -- loop-variable fvars and their ids
  ctr    : IO.Ref Nat             -- fresh loop ids
  depth  : Nat := 0               -- inlining depth of ℤ-valued helpers

abbrev TrM := ExceptT String MetaM

/-- Block with a reason. (`bail` alone is ambiguous here: MetaM's `Exception` is also throwable.) -/
def bail {α : Type} (msg : String) : TrM α := throwThe String msg

def fresh (c : Ctx) : TrM Nat := do
  let n ← c.ctr.get
  c.ctr.set (n + 1)
  return n

/-- The identity `fun k : ℕ => k`: the element of a plain range is its loop counter. -/
def idElem : Expr := .lam `k (mkConst ``Nat) (.bvar 0) .default

mutual

/-- Translate a ℕ-valued expression. -/
partial def tr (c : Ctx) (e : Expr) : TrM E := do
  let e := e.consumeMData
  if let .letE _ _ v b _ := e then return ← tr c (b.instantiate1 v)
  if e.isApp && e.getAppFn.isLambda then return ← tr c e.headBeta   -- local `let f := fun …` applied
  if let some n := natLit? e then return .lit n
  if e.isFVar then
    -- the recursion counter m is recognised BEFORE argument lookup (in the step, args[j] is m)
    if c.idx? == some e then return .idx
    if let some (_, id) := c.loops.find? (·.1 == e) then return .lvar id
    if let some i := c.args.findIdx? (· == e) then return .arg i
    bail "free variable not an argument"
  if let some (op, a, b) := binOp? e then return .bin op (← tr c a) (← tr c b)
  if e.isAppOfArity ``Nat.succ 1 then return .bin "add" (← tr c e.appArg!) (.lit 1)
  let (fn, args) := e.getAppFnArgs
  -- min / max on ℕ
  if (fn == ``Min.min || fn == ``Max.max) && args.size == 4 && isNatTy args[0]! then
    return .prim (if fn == ``Min.min then "min" else "max") [← tr c args[2]!, ← tr c args[3]!]
  -- builtins
  if fn == ``Nat.gcd && args.size == 2 then return .prim "gcd" [← tr c args[0]!, ← tr c args[1]!]
  if fn == ``Nat.lcm && args.size == 2 then return .prim "lcm" [← tr c args[0]!, ← tr c args[1]!]
  if fn == `Nat.choose && args.size == 2 then return .prim "choose" [← tr c args[0]!, ← tr c args[1]!]
  if fn == `Nat.factorial && args.size == 1 then return .prim "fact" [← tr c args[0]!]
  if fn == `Nat.sqrt && args.size == 1 then return .prim "sqrt" [← tr c args[0]!]
  if fn == `Nat.minFac && args.size == 1 then return .prim "minfac" [← tr c args[0]!]
  -- ℚ → ℕ
  if fn == `Rat.den && args.size == 1 then return .prim "qden" [← trQ c args[0]!]
  -- ℤ → ℕ
  if fn == ``Int.toNat && args.size == 1 then return .prim "tonat" [← trI c args[0]!]
  if fn == ``Int.natAbs && args.size == 1 then return .prim "natabs" [← trI c args[0]!]
  -- MathIR v5 builtins
  if fn == ``Nat.pred && args.size == 1 then return .bin "sub" (← tr c args[0]!) (.lit 1)
  if fn == `Nat.centralBinom && args.size == 1 then
    let n ← tr c args[0]!
    return .prim "choose" [.bin "mul" (.lit 2) n, n]
  if fn == `Nat.fermatNumber && args.size == 1 then
    return .bin "add" (.bin "pow" (.lit 2) (.bin "pow" (.lit 2) (← tr c args[0]!))) (.lit 1)
  if (fn == ``HXor.hXor && args.size == 6 && isNatTy args[0]! && isNatTy args[1]!) then
    return .prim "xor" [← tr c args[4]!, ← tr c args[5]!]
  if fn == ``Nat.xor && args.size == 2 then return .prim "xor" [← tr c args[0]!, ← tr c args[1]!]
  if fn == ``Bool.toNat && args.size == 1 then return ← trBool c args[0]!
  -- `if h : c then t else e` whose branches do not use `h`
  if fn == ``dite && args.size == 5 && isNatTy args[0]! then
    let br (b : Expr) : TrM Expr := do
      match b.consumeMData with
      | .lam _ _ body _ => if body.hasLooseBVar 0 then bail "dependent if-then-else" else pure (body.lowerLooseBVars 1 1)
      | _ => bail "dependent if-then-else"
    return .ite (← trProp c args[1]!) (← tr c (← br args[3]!)) (← tr c (← br args[4]!))
  -- MathIR v3 builtins (exact semantics re-checked against the compiled corpus by the fidelity check)
  if fn == ``id && args.size == 2 then return ← tr c args[1]!
  if fn == `Nat.fib && args.size == 1 then return .prim "fib" [← tr c args[0]!]
  if fn == `Nat.log && args.size == 2 then return .prim "log" [← tr c args[0]!, ← tr c args[1]!]
  if fn == ``Nat.log2 && args.size == 1 then return .prim "log2" [← tr c args[0]!]
  if fn == `padicValNat && args.size == 2 then return .prim "padic" [← tr c args[0]!, ← tr c args[1]!]
  -- φ n = #{a ∈ range n | n.Coprime a}
  if fn == `Nat.totient && args.size == 1 then
    let n ← tr c args[0]!
    let id ← fresh c
    return .fold "count" id (.lit 0) n false (.cmp "eq" (.prim "gcd" [n, .lvar id]) (.lit 1)) (.lit 1)
  -- arithmetic functions applied through `DFunLike.coe`: σ k, ω, Ω
  if fn == `DFunLike.coe && args.size == 6 then
    let F := args[0]!.consumeMData
    unless F.getAppFn.isConstOf `ArithmeticFunction && F.getAppNumArgs == 2 && isNatTy F.getAppArgs[0]! do
      bail s!"unsupported: DFunLike.coe"
    let x ← tr c args[5]!
    let (g, gargs) := args[4]!.consumeMData.getAppFnArgs
    if g == `ArithmeticFunction.sigma && gargs.size == 1 then
      let k ← tr c gargs[0]!
      let id ← fresh c
      return .fold "sum" id (.lit 1) x true (.prim "dvd" [.lvar id, x]) (.bin "pow" (.lvar id) k)
    if g == `ArithmeticFunction.cardDistinctFactors && gargs.size == 0 then
      let id ← fresh c
      return .fold "count" id (.lit 1) x true (.and (.prim "dvd" [.lvar id, x]) (.prim "prime" [.lvar id])) (.lit 1)
    if g == `ArithmeticFunction.cardFactors && gargs.size == 0 then return .prim "bigomega" [x]
    bail s!"unsupported: arithmetic function {g}"
  -- digit functions and prime-factor list lengths
  if fn == ``List.sum && args.size == 4 && isNatTy args[0]! then
    let (g, ga) := (args[3]!.consumeMData).getAppFnArgs
    if g == `Nat.digits && ga.size == 2 then return .prim "digsum" [← tr c ga[0]!, ← tr c ga[1]!]
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← lsource c id args[3]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (elem.beta #[x])
    return .fold "sum" id lo hi incl filt body
  if fn == ``List.length && args.size == 2 && isNatTy args[0]! then
    let (g, ga) := (args[1]!.consumeMData).getAppFnArgs
    if g == `Nat.digits && ga.size == 2 then return .prim "diglen" [← tr c ga[0]!, ← tr c ga[1]!]
    if g == `Nat.primeFactorsList && ga.size == 1 then return .prim "bigomega" [← tr c ga[0]!]
    if g == `List.dedup && ga.size == 3 then
      let (h, ha) := (ga[2]!.consumeMData).getAppFnArgs
      if h == `Nat.primeFactorsList && ha.size == 1 then
        let x ← tr c ha[0]!
        let id ← fresh c
        return .fold "count" id (.lit 1) x true (.and (.prim "dvd" [.lvar id, x]) (.prim "prime" [.lvar id])) (.lit 1)
    let id ← fresh c
    let (lo, hi, incl, filt, _) ← lsource c id args[1]!
    return .fold "count" id lo hi incl filt (.lit 1)
  -- l.foldl f init over a range-based list: an accumulator loop
  if fn == ``List.foldl && args.size == 5 && isNatTy args[0]! && isNatTy args[1]! then
    let id ← fresh c
    let acc := accBase + (← fresh c)
    let (lo, hi, incl, filt, elem) ← lsource c id args[4]!
    let init ← tr c args[3]!
    let body ← withLocalDeclD `a (mkConst ``Nat) fun a => withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := (c.loops.push (x, id)).push (a, acc) } (args[2]!.beta #[a, elem.beta #[x]])
    return .iter id acc lo hi incl filt init body
  -- l.headD d: the first element, or d for the empty list (accumulator: 0 = none yet, else elem + 1)
  if fn == ``List.headD && args.size == 3 && isNatTy args[0]! then
    let id ← fresh c
    let acc := accBase + (← fresh c)
    let (lo, hi, incl, filt, elem) ← lsource c id args[1]!
    let e ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (elem.beta #[x])
    let first := E.iter id acc lo hi incl filt (.lit 0)
      (.ite (.cmp "eq" (.lvar acc) (.lit 0)) (.bin "add" e (.lit 1)) (.lvar acc))
    return .ite (.cmp "eq" first (.lit 0)) (← tr c args[2]!) (.bin "sub" first (.lit 1))
  -- ofDigits b (digits b n).reverse : digit reversal (same base on both sides)
  if fn == `Nat.ofDigits && args.size == 4 && isNatTy args[0]! then
    let (g, ga) := (args[3]!.consumeMData).getAppFnArgs
    if g == ``List.reverse && ga.size == 2 then
      let (h, ha) := (ga[1]!.consumeMData).getAppFnArgs
      if h == `Nat.digits && ha.size == 2 then
        unless (← isDefEq args[2]! ha[0]!) do bail "unsupported: Nat.ofDigits (bases differ)"
        return .prim "digrev" [← tr c args[2]!, ← tr c ha[1]!]
    bail "unsupported: Nat.ofDigits"
  -- Finset.sup f over a ℕ source, into ℕ (⊥ = 0)
  if fn == `Finset.sup && args.size == 6 then
    unless isNatTy args[0]! && isNatTy args[1]! do bail "Finset.sup over a non-ℕ type"
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← source c id args[4]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (args[5]!.beta #[elem.beta #[x]])
    return .fold "max" id lo hi incl filt body
  -- Finset.lcm f over a ℕ source, into ℕ (lcm ∅ = 1; normalize is the identity on ℕ)
  if fn == `Finset.lcm && args.size == 6 then
    unless isNatTy args[0]! && isNatTy args[1]! do bail "Finset.lcm over a non-ℕ type"
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← source c id args[4]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (args[5]!.beta #[elem.beta #[x]])
    return .fold "lcm" id lo hi incl filt body
  -- if-then-else on a decidable predicate
  if fn == ``ite && args.size == 5 then
    unless isNatTy args[0]! do bail "ite at a non-ℕ type"
    return .ite (← trProp c args[1]!) (← tr c args[3]!) (← tr c args[4]!)
  -- ∑ / ∏ over a ℕ range
  if (fn == `Finset.sum || fn == `Finset.prod) && args.size == 5 then
    unless isNatTy args[0]! && isNatTy args[1]! do bail s!"{fn} over a non-ℕ type"
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← source c id args[3]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (args[4]!.beta #[elem.beta #[x]])
    return .fold (if fn == `Finset.sum then "sum" else "prod") id lo hi incl filt body
  -- Finset.card of a (filtered) ℕ range
  if fn == `Finset.card && args.size == 2 then
    unless isNatTy args[0]! do bail "Finset.card over a non-ℕ type"
    let id ← fresh c
    let (lo, hi, incl, filt, _) ← source c id args[1]!
    return .fold "count" id lo hi incl filt (.lit 1)
  -- recursive call
  if fn == c.self then
    let some j := c.recArg | bail "recursion in a non-recursive equation"
    let some m := c.idx? | bail "recursive call outside the step equation"
    if args.size != c.args.size then bail "partial recursive call"
    for h : i in [0:args.size] do
      if i != j then
        unless args[i] == c.args[i]! do bail "non-primitive recursion (arguments change)"
    match offsetPattern? args[j]! with
    | some (m', d) => if m' == m && d < c.K then return .prev d else bail "recursive call outside the lookback window"
    | none => bail "recursive call on a non-offset argument"
  -- call to another ℕ function: translated only if that function is translated (closure later)
  if fn != .anonymous then
    let ci ← getConstInfo fn
    let isNatFn ← forallTelescope ci.type fun xs body => do
      if !isNatTy body then return false
      for x in xs do
        unless isNatTy (← inferType x) do return false
      return xs.size == args.size && xs.size ≥ 1
    unless isNatFn do bail s!"unsupported: {fn}"
    return .call fn (← args.toList.mapM (tr c))
  bail s!"unsupported expression ({e.ctorName})"

/-- Translate a decidable proposition to a boolean (0 / 1) expression. -/
partial def trProp (c : Ctx) (p : Expr) : TrM E := do
  let p := p.consumeMData
  if p.isApp && p.getAppFn.isLambda then return ← trProp c p.headBeta   -- local `let f := fun …` applied
  if p.isConstOf ``True then return .lit 1
  if p.isConstOf ``False then return .lit 0
  let (fn, args) := p.getAppFnArgs
  match fn, args with
  | ``LT.lt, #[ty, _, a, b] =>
    if isNatTy ty then return .cmp "lt" (← tr c a) (← tr c b)
    else if isIntTy ty then return .cmp "ilt" (← trI c a) (← trI c b)
    else bail "comparison at a non-ℕ type"
  | ``LE.le, #[ty, _, a, b] =>
    if isNatTy ty then return .cmp "le" (← tr c a) (← tr c b)
    else if isIntTy ty then return .cmp "ile" (← trI c a) (← trI c b)
    else bail "comparison at a non-ℕ type"
  | ``GT.gt, #[ty, _, a, b] =>
    if isNatTy ty then return .cmp "lt" (← tr c b) (← tr c a)
    else if isIntTy ty then return .cmp "ilt" (← trI c b) (← trI c a)
    else bail "comparison at a non-ℕ type"
  | ``GE.ge, #[ty, _, a, b] =>
    if isNatTy ty then return .cmp "le" (← tr c b) (← tr c a)
    else if isIntTy ty then return .cmp "ile" (← trI c b) (← trI c a)
    else bail "comparison at a non-ℕ type"
  | ``Eq, #[ty, a, b] =>
    if isNatTy ty then return .cmp "eq" (← tr c a) (← tr c b)
    else if isIntTy ty then return .cmp "ieq" (← trI c a) (← trI c b)
    else if ty.isConstOf ``Bool then return .cmp "eq" (← trBool c a) (← trBool c b)
    else bail "equality at a non-ℕ type"
  | ``Ne, #[ty, a, b] =>
    if isNatTy ty then return .not (.cmp "eq" (← tr c a) (← tr c b))
    else if isIntTy ty then return .not (.cmp "ieq" (← trI c a) (← trI c b))
    else if ty.isConstOf ``Bool then return .not (.cmp "eq" (← trBool c a) (← trBool c b))
    else bail "≠ at a non-ℕ type"
  | ``Not, #[q] => return .not (← trProp c q)
  | ``And, #[q, r] => return .and (← trProp c q) (← trProp c r)
  | ``Or, #[q, r] => return .or (← trProp c q) (← trProp c r)
  | ``Dvd.dvd, #[ty, _, a, b] => if isNatTy ty then return .prim "dvd" [← tr c a, ← tr c b] else bail "∣ at a non-ℕ type"
  | `Nat.Prime, #[n] => return .prim "prime" [← tr c n]
  | `Nat.Coprime, #[a, b] => return .cmp "eq" (.prim "gcd" [← tr c a, ← tr c b]) (.lit 1)
  | `Even, #[ty, _, n] => if isNatTy ty then return .cmp "eq" (.bin "mod" (← tr c n) (.lit 2)) (.lit 0) else bail "Even at a non-ℕ type"
  | `Odd, #[ty, _, n] => if isNatTy ty then return .cmp "eq" (.bin "mod" (← tr c n) (.lit 2)) (.lit 1) else bail "Odd at a non-ℕ type"
  | _, _ => bail s!"unsupported predicate: {fn}"

/-- Translate a `Bool` to a 0 / 1 expression. -/
partial def trBool (c : Ctx) (b : Expr) : TrM E := do
  let b := b.consumeMData
  if let .letE _ _ v body _ := b then return ← trBool c (body.instantiate1 v)
  if b.isApp && b.getAppFn.isLambda then return ← trBool c b.headBeta
  if b.isConstOf ``Bool.true then return .lit 1
  if b.isConstOf ``Bool.false then return .lit 0
  let (fn, args) := b.getAppFnArgs
  match fn, args with
  | ``Decidable.decide, #[p, _] => trProp c p
  | ``and, #[x, y] => return .and (← trBool c x) (← trBool c y)
  | ``or, #[x, y] => return .or (← trBool c x) (← trBool c y)
  | ``not, #[x] => return .not (← trBool c x)
  | ``Nat.testBit, #[n, i] =>
    -- testBit n i ↔ (n / 2^i) % 2 = 1  (the wide fallback covers i ≥ 64)
    return .cmp "eq" (.bin "mod" (.bin "div" (← tr c n) (.bin "pow" (.lit 2) (← tr c i))) (.lit 2)) (.lit 1)
  | ``BEq.beq, #[ty, _, x, y] =>
    if isNatTy ty then return .cmp "eq" (← tr c x) (← tr c y) else bail "== at a non-ℕ type"
  | ``bne, #[ty, _, x, y] =>
    if isNatTy ty then return .not (.cmp "eq" (← tr c x) (← tr c y)) else bail "!= at a non-ℕ type"
  | ``Nat.ble, #[x, y] => return .cmp "le" (← tr c x) (← tr c y)
  | ``Nat.blt, #[x, y] => return .cmp "lt" (← tr c x) (← tr c y)
  | ``Nat.beq, #[x, y] => return .cmp "eq" (← tr c x) (← tr c y)
  | _, _ => bail s!"unsupported (Bool): {fn}"

/-- Translate a ℚ-valued expression (left via `Rat.num` / `Rat.den`). -/
partial def trQ (c : Ctx) (e : Expr) : TrM E := do
  let e := e.consumeMData
  if let .letE _ _ v b _ := e then return ← trQ c (b.instantiate1 v)
  if e.isApp && e.getAppFn.isLambda then return ← trQ c e.headBeta
  let (fn, args) := e.getAppFnArgs
  if fn == ``OfNat.ofNat && args.size == 3 && isRatTy args[0]! then
    match args[1]!.consumeMData with
    | .lit (.natVal k) => return .prim "qofnat" [.lit k]
    | _ => bail "ℚ literal"
  if (fn == ``Nat.cast || fn == ``NatCast.natCast) && args.size == 3 && isRatTy args[0]! then
    return .prim "qofnat" [← tr c args[2]!]
  if (fn == ``Int.cast || fn == ``IntCast.intCast) && args.size == 3 && isRatTy args[0]! then
    return .prim "qofint" [← trI c args[2]!]
  if fn == ``Neg.neg && args.size == 3 && isRatTy args[0]! then return .prim "qneg" [← trQ c args[2]!]
  if fn == `Inv.inv && args.size == 3 && isRatTy args[0]! then return .prim "qinv" [← trQ c args[2]!]
  if (fn == ``HAdd.hAdd || fn == ``HSub.hSub || fn == ``HMul.hMul || fn == ``HDiv.hDiv) && args.size == 6 &&
      isRatTy args[0]! && isRatTy args[1]! && isRatTy args[2]! then
    let op := if fn == ``HAdd.hAdd then "qadd" else if fn == ``HSub.hSub then "qsub"
      else if fn == ``HMul.hMul then "qmul" else "qdiv"
    return .bin op (← trQ c args[4]!) (← trQ c args[5]!)
  if fn == ``HPow.hPow && args.size == 6 && isRatTy args[0]! && isNatTy args[1]! && isRatTy args[2]! then
    return .bin "qpow" (← trQ c args[4]!) (← tr c args[5]!)
  if fn == ``ite && args.size == 5 && isRatTy args[0]! then
    return .ite (← trProp c args[1]!) (← trQ c args[3]!) (← trQ c args[4]!)
  if (fn == `Finset.sum || fn == `Finset.prod) && args.size == 5 && isNatTy args[0]! && isRatTy args[1]! then
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← source c id args[3]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      trQ { c with loops := c.loops.push (x, id) } (args[4]!.beta #[elem.beta #[x]])
    return .fold (if fn == `Finset.sum then "qsum" else "qprod") id lo hi incl filt body
  -- a non-recursive ℚ-valued helper ℕ^k → ℚ: inline its body (bounded depth)
  if fn != .anonymous && c.depth < 4 then
    let ci ← getConstInfo fn
    if let some v := ci.value? then
      let ok ← forallTelescope ci.type fun xs body => do
        if !isRatTy body || xs.size != args.size || xs.isEmpty then return false
        for x in xs do
          unless isNatTy (← inferType x) do return false
        return true
      if ok then return ← trQ { c with depth := c.depth + 1 } (v.beta args)
  bail s!"unsupported (ℚ): {fn}"

/-- Translate a ℤ-valued expression (ℤ subterms enter from ℕ via casts / literals and leave via
`toNat`, `natAbs` or a comparison). -/
partial def trI (c : Ctx) (e : Expr) : TrM E := do
  let e := e.consumeMData
  if let .letE _ _ v b _ := e then return ← trI c (b.instantiate1 v)
  if e.isApp && e.getAppFn.isLambda then return ← trI c e.headBeta   -- local `let f := fun …` applied
  let (fn, args) := e.getAppFnArgs
  -- literals and casts ℕ → ℤ
  if fn == ``OfNat.ofNat && args.size == 3 && isIntTy args[0]! then
    match args[1]!.consumeMData with
    | .lit (.natVal k) => return .prim "ofnat" [.lit k]
    | _ => bail "ℤ literal"
  if fn == ``Int.ofNat && args.size == 1 then return .prim "ofnat" [← tr c args[0]!]
  if (fn == ``Nat.cast || fn == ``NatCast.natCast) && args.size == 3 && isIntTy args[0]! then
    return .prim "ofnat" [← tr c args[2]!]
  if fn == ``Neg.neg && args.size == 3 && isIntTy args[0]! then return .prim "ineg" [← trI c args[2]!]
  if fn == ``Int.neg && args.size == 1 then return .prim "ineg" [← trI c args[0]!]
  if fn == ``Int.sign && args.size == 1 then return .prim "isign" [← trI c args[0]!]
  if fn == `Rat.num && args.size == 1 then return .prim "qnum" [← trQ c args[0]!]
  -- arithmetic
  if (fn == ``HAdd.hAdd || fn == ``HSub.hSub || fn == ``HMul.hMul) && args.size == 6 &&
      isIntTy args[0]! && isIntTy args[1]! && isIntTy args[2]! then
    let op := if fn == ``HAdd.hAdd then "iadd" else if fn == ``HSub.hSub then "isub" else "imul"
    return .bin op (← trI c args[4]!) (← trI c args[5]!)
  if (fn == ``Int.add || fn == ``Int.sub || fn == ``Int.mul) && args.size == 2 then
    let op := if fn == ``Int.add then "iadd" else if fn == ``Int.sub then "isub" else "imul"
    return .bin op (← trI c args[0]!) (← trI c args[1]!)
  if fn == ``HPow.hPow && args.size == 6 && isIntTy args[0]! && isNatTy args[1]! && isIntTy args[2]! then
    return .bin "ipow" (← trI c args[4]!) (← tr c args[5]!)
  -- if-then-else
  if fn == ``ite && args.size == 5 && isIntTy args[0]! then
    return .ite (← trProp c args[1]!) (← trI c args[3]!) (← trI c args[4]!)
  -- ∑ / ∏ of ℤ over a ℕ source (`Finset.sum {ι M} [AddCommMonoid M] s f`: index type first)
  if (fn == `Finset.sum || fn == `Finset.prod) && args.size == 5 && isNatTy args[0]! && isIntTy args[1]! then
    let id ← fresh c
    let (lo, hi, incl, filt, elem) ← source c id args[3]!
    let body ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      trI { c with loops := c.loops.push (x, id) } (args[4]!.beta #[elem.beta #[x]])
    return .fold (if fn == `Finset.sum then "isum" else "iprod") id lo hi incl filt body
  -- a non-recursive ℤ-valued helper ℕ^k → ℤ: inline its body (bounded depth). A recursive one
  -- elaborates to a recursor / WellFounded.fix and is rejected while translating the body.
  if fn != .anonymous && c.depth < 4 then
    let ci ← getConstInfo fn
    if let some v := ci.value? then
      let ok ← forallTelescope ci.type fun xs body => do
        if !isIntTy body || xs.size != args.size || xs.isEmpty then return false
        for x in xs do
          unless isNatTy (← inferType x) do return false
        return true
      if ok then return ← trI { c with depth := c.depth + 1 } (v.beta args)
  bail s!"unsupported (ℤ): {fn}"

/-- A finite set of ℕ enumerated by a loop: `(lo, hi, inclusive, filter, elem)`. The loop counter
runs over [lo, hi] / [lo, hi) in increasing order; `filter` is a boolean expression over loop
variable `id`; `elem : ℕ → ℕ` (a Lean lambda) maps the counter to the set element. Every source
enumerates each element at most once (an image keeps only the first occurrence), so sums,
products and counts over it are the Finset ones. -/
partial def source (c : Ctx) (id : Nat) (s : Expr) : TrM (E × E × Bool × E × Expr) := do
  let s := s.consumeMData
  let (fn, args) := s.getAppFnArgs
  if fn == `Finset.range && args.size == 1 then
    return (.lit 0, ← tr c args[0]!, false, .lit 1, idElem)
  if (fn == `Finset.Icc || fn == `Finset.Ico || fn == `Finset.Ioc || fn == `Finset.Ioo) && args.size ≥ 3 then
    unless isNatTy args[0]! do bail s!"{fn} over a non-ℕ type"
    let a ← tr c args[args.size - 2]!
    let b ← tr c args[args.size - 1]!
    let lo := if fn == `Finset.Ioc || fn == `Finset.Ioo then .bin "add" a (.lit 1) else a
    let incl := fn == `Finset.Icc || fn == `Finset.Ioc
    return (lo, b, incl, .lit 1, idElem)
  if fn == `Finset.filter && args.size == 4 then
    unless isNatTy args[0]! do bail "Finset.filter over a non-ℕ type"
    let (lo, hi, incl, f0, elem) ← source c id args[3]!
    let f1 ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      trProp { c with loops := c.loops.push (x, id) } (args[1]!.beta #[elem.beta #[x]])
    let filt := match f0 with | .lit 1 => f1 | _ => .and f0 f1
    return (lo, hi, incl, filt, elem)
  -- divisors n = {d ∈ Ico 1 (n + 1) | d ∣ n};  properDivisors n = {d ∈ Ico 1 n | d ∣ n}
  -- primeFactors n = the primes dividing n (∅ for n = 0);  primesBelow n = {p ∈ range n | p.Prime}
  if (fn == `Nat.divisors || fn == `Nat.properDivisors || fn == `Nat.primeFactors) && args.size == 1 then
    let n ← tr c args[0]!
    let dv := E.prim "dvd" [.lvar id, n]
    if fn == `Nat.divisors then return (.lit 1, n, true, dv, idElem)
    if fn == `Nat.properDivisors then return (.lit 1, n, false, dv, idElem)
    return (.lit 1, n, true, .and dv (.prim "prime" [.lvar id]), idElem)
  if fn == `Nat.primesBelow && args.size == 1 then
    return (.lit 0, ← tr c args[0]!, false, .prim "prime" [.lvar id], idElem)
  -- image f s (ℕ → ℕ): enumerate s, map by f, keep an element only at its first occurrence
  -- (no earlier counter value of s with the same image)
  if fn == `Finset.image && args.size == 5 then
    unless isNatTy args[0]! && isNatTy args[1]! do bail "Finset.image over a non-ℕ type"
    let f := args[3]!
    let (lo, hi, incl, f0, e0) ← source c id args[4]!
    let elem : Expr := .lam `k (mkConst ``Nat) (.app f (.app e0 (.bvar 0))) .default
    let id' ← fresh c
    let (lo', _, _, f0', e0') ← source c id' args[4]!
    let elem' : Expr := .lam `k (mkConst ``Nat) (.app f (.app e0' (.bvar 0))) .default
    let eK ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      tr { c with loops := c.loops.push (x, id) } (elem.beta #[x])
    let eJ ← withLocalDeclD `k (mkConst ``Nat) fun y =>
      tr { c with loops := c.loops.push (y, id') } (elem'.beta #[y])
    let earlier := E.fold "count" id' lo' (.lvar id) false (.and f0' (.cmp "eq" eJ eK)) (.lit 1)
    let first := E.cmp "eq" earlier (.lit 0)
    let filt := match f0 with | .lit 1 => first | _ => .and f0 first
    return (lo, hi, incl, filt, elem)
  bail s!"unsupported Finset source: {fn}"

/-- A list of ℕ built from a range: `(lo, hi, inclusive, filter, elem)` like `source`, but in list
order and keeping duplicates (`map` does not deduplicate). -/
partial def lsource (c : Ctx) (id : Nat) (l : Expr) : TrM (E × E × Bool × E × Expr) := do
  let l := l.consumeMData
  if let .letE _ _ v b _ := l then return ← lsource c id (b.instantiate1 v)
  let (fn, args) := l.getAppFnArgs
  if fn == ``List.range && args.size == 1 then
    return (.lit 0, ← tr c args[0]!, false, .lit 1, idElem)
  if fn == `List.Ico && args.size == 2 then
    return (← tr c args[0]!, ← tr c args[1]!, false, .lit 1, idElem)
  if fn == ``List.filter && args.size == 3 && isNatTy args[0]! then
    let (lo, hi, incl, f0, elem) ← lsource c id args[2]!
    let f1 ← withLocalDeclD `k (mkConst ``Nat) fun x =>
      trBool { c with loops := c.loops.push (x, id) } (args[1]!.beta #[elem.beta #[x]])
    let filt := match f0 with | .lit 1 => f1 | _ => .and f0 f1
    return (lo, hi, incl, filt, elem)
  if fn == ``List.map && args.size == 4 && isNatTy args[0]! && isNatTy args[1]! then
    let (lo, hi, incl, filt, e0) ← lsource c id args[3]!
    return (lo, hi, incl, filt, .lam `k (mkConst ``Nat) (.app args[2]! (.app e0 (.bvar 0))) .default)
  bail s!"unsupported list: {fn}"

end

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
  let ctr ← IO.mkRef 0
  let eqns? ← try getEqnsFor? n catch _ => pure none
  let eqns := eqns?.getD #[]
  if eqns.isEmpty then
    let ci ← getConstInfo n
    let some v := ci.value? | return .error "no definition body"
    return ← lambdaTelescope v fun xs body => do
      if xs.size != arity then return .error "body arity differs from type arity"
      match ← (tr { self := n, args := xs, idx? := none, recArg := none, ctr } body).run with
      | .ok e => return .ok (.direct arity e)
      | .error r => return .error r
  -- classify every equation by its (single) non-variable argument position
  let mut bases : Array (Nat × Expr × Array Expr) := #[]     -- (literal, rhs, lhs args)
  let mut steps : Array (Nat × Expr × Expr × Array Expr) := #[]   -- (K, m, rhs, lhs args)
  let mut directs : Array (Expr × Array Expr) := #[]
  let mut pos? : Option Nat := none
  for eqn in eqns do
    let thm ← getConstInfo eqn
    let r ← forallTelescope thm.type fun _ eq => do
      let some (_, lhs, rhs) := eq.eq? | return Except.error "equation is not an Eq"
      let largs := lhs.getAppArgs
      if largs.size != arity then return .error "partial application in equation"
      let nonVar := (List.range arity).filter (fun i => !largs[i]!.isFVar)
      match nonVar with
      | [] => return .ok (none, 0, none, rhs, largs)
      | [j] =>
        let pat := largs[j]!
        if let some k := natLit? pat then return .ok (some j, k, none, rhs, largs)
        match offsetPattern? pat with
        | some (m, k) => if k ≥ 1 then return .ok (some j, k, some m, rhs, largs) else return .error "recursion pattern is not literal / m+K"
        | none => return .error "recursion pattern is not literal / m+K"
      | _ => return .error "patterns on more than one argument"
    match r with
    | .error e => return .error e
    | .ok (none, _, _, rhs, largs) => directs := directs.push (rhs, largs)
    | .ok (some j, k, m?, rhs, largs) =>
      if pos? != none && pos? != some j then return .error "equations recurse on different arguments"
      pos? := some j
      match m? with
      | none => bases := bases.push (k, rhs, largs)
      | some m => steps := steps.push (k, m, rhs, largs)
  if pos? == none then
    unless directs.size == 1 do return .error s!"{directs.size} unconditional equations"
    let (rhs, largs) := directs[0]!
    return ← match ← (tr { self := n, args := largs, idx? := none, recArg := none, ctr } rhs).run with
      | .ok e => pure (.ok (.direct arity e))
      | .error r => pure (.error r)
  let some j := pos? | return .error "unreachable"
  unless directs.isEmpty do return .error "mixed pattern / non-pattern equations"
  unless steps.size == 1 do return .error s!"{steps.size} step equations (need exactly one)"
  let (K, _, _, _) := steps[0]!
  let lits := (bases.map (·.1)).qsort (· < ·)
  -- base cases must be exactly 0..B-1 with B ≥ K. With overlapping patterns (e.g. `| 0 | 1 | n+1`)
  -- B > K: the step equation then holds only for arguments ≥ B (Lean matches earlier patterns
  -- first), which is reproduced below by selecting the extra base values inside the step.
  let B := lits.size
  unless B ≥ K && lits == (List.range B).toArray do
    return .error s!"base cases {lits.toList} do not cover 0..{K}-1"
  -- re-open each equation to translate it (fvars are only valid inside their telescope)
  let mut baseE : Array (Nat × E) := #[]
  let mut stepE? : Option E := none
  for eqn in eqns do
    let thm ← getConstInfo eqn
    let r ← forallTelescope thm.type fun _ eq => do
      let some (_, lhs, rhs) := eq.eq? | return Except.error "equation is not an Eq"
      let largs := lhs.getAppArgs
      let pat := largs[j]!
      if let some k := natLit? pat then
        match ← (tr { self := n, args := largs.set! j (mkNatLit k), idx? := none, recArg := some j, ctr } rhs).run with
        | .ok e => return .ok (some k, e)
        | .error r => return .error r
      let some (m, _) := offsetPattern? pat | return .error "unreachable pattern"
      match ← (tr { self := n, args := largs.set! j m, idx? := some m, recArg := some j, K, ctr } rhs).run with
      | .ok e => return .ok (none, e)
      | .error r => return .error r
    match r with
    | .error e => return .error e
    | .ok (some k, e) => baseE := baseE.push (k, e)
    | .ok (none, e) => stepE? := some e
  let some stepE := stepE? | return .error "missing step equation"
  let basesSorted := (baseE.qsort (fun a b => a.1 < b.1)).toList.map (·.2)
  -- extra base values f c for K ≤ c < B: inside the step (idx m computes f (m + K)), select them
  let mut step := stepE
  for c in (List.range B).reverse do
    if c ≥ K then
      step := .ite (.cmp "eq" .idx (.lit (c - K))) (basesSorted.getD c (.lit 0)) step
  return .ok (.recur arity j (basesSorted.take K) step)

/-! ## Names -/

def sanitize (s : String) : String :=
  String.mk (s.toList.map fun c => if c.isAlphanum && c.toNat < 128 then c else '_')

/-! ## C emission -/

structure CG where
  lines : Array String := #[]
  tmp   : Nat := 0

abbrev CGM := StateM CG

def emitC (l : String) : CGM Unit := modify fun s => { s with lines := s.lines.push l }
def freshC : CGM String := modifyGet fun s => (s!"t{s.tmp}", { s with tmp := s.tmp + 1 })

def cPrimOverflowing : List String := ["gcd", "lcm", "fact", "choose", "sqrt", "minfac", "fib", "digrev"]

mutual
/-- Emit C statements computing `e`; returns the C expression holding its value. -/
partial def cExpr (sym : Name → String) (ind : String) : E → CGM String
  | .lit n => pure s!"{n}ULL"
  | .arg i => pure s!"a{i}"
  | .idx => pure "i"
  | .prev j => pure s!"w{j}"
  | .lvar id => pure s!"v{id}"
  | .bin op a b => do
    if op.startsWith "i" then emitC "#error \"ill-typed MathIR: integer operation in a natural-number position\""
    let x ← cExpr sym ind a
    let y ← cExpr sym ind b
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if (lm2_{op}({x}, {y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .prim op as => do
    if op == "qden" then
      -- ℚ subterms run only on the exact wide path: the fast path hands over
      let t ← freshC
      emitC s!"{ind}uint64_t {t} = 0ULL; if (1) return LM2_OVERFLOW;"
      return t
    if op == "tonat" || op == "natabs" then
      let x ← cExprI sym ind (as.headD default)
      let t ← freshC
      emitC s!"{ind}uint64_t {t} = lm2_{op}({x});"
      return t
    if op ∈ ["ofnat", "ineg", "isign"] then emitC "#error \"ill-typed MathIR: integer operation in a natural-number position\""
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← cExpr sym ind a)
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    let callArgs := ", ".intercalate vs.toList
    if op ∈ cPrimOverflowing then
      emitC s!"{ind}if (lm2_{op}({callArgs}, &{t})) return LM2_OVERFLOW;"
    else
      let fnName := if op == "prime" then "isprime" else op
      emitC s!"{ind}{t} = lm2_{fnName}({callArgs});"
    return t
  | .cmp k a b => do
    let ints := k.startsWith "i"
    let x ← if ints then cExprI sym ind a else cExpr sym ind a
    let y ← if ints then cExprI sym ind b else cExpr sym ind b
    let t ← freshC
    let op := match k with | "lt" | "ilt" => "<" | "le" | "ile" => "<=" | _ => "=="
    emitC s!"{ind}uint64_t {t} = ({x} {op} {y}) ? 1ULL : 0ULL;"
    return t
  | .not a => do
    let x ← cExpr sym ind a
    let t ← freshC
    emitC s!"{ind}uint64_t {t} = ({x} == 0ULL) ? 1ULL : 0ULL;"
    return t
  | .and a b => do
    let x ← cExpr sym ind a
    let t ← freshC
    emitC s!"{ind}uint64_t {t} = 0ULL;"
    emitC s!"{ind}if ({x} != 0ULL) \{"
    let y ← cExpr sym (ind ++ "  ") b
    emitC s!"{ind}  {t} = ({y} != 0ULL) ? 1ULL : 0ULL;"
    emitC s!"{ind}}"
    return t
  | .or a b => do
    let x ← cExpr sym ind a
    let t ← freshC
    emitC s!"{ind}uint64_t {t} = 1ULL;"
    emitC s!"{ind}if ({x} == 0ULL) \{"
    let y ← cExpr sym (ind ++ "  ") b
    emitC s!"{ind}  {t} = ({y} != 0ULL) ? 1ULL : 0ULL;"
    emitC s!"{ind}}"
    return t
  | .ite c th el => do
    let x ← cExpr sym ind c
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if ({x} != 0ULL) \{"
    let r1 ← cExpr sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExpr sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .fold op id lo hi incl filt body => do
    if op.startsWith "i" then emitC "#error \"ill-typed MathIR: integer fold in a natural-number position\""
    let l ← cExpr sym ind lo
    let h ← cExpr sym ind hi
    let t ← freshC
    let v := s!"v{id}"
    emitC s!"{ind}uint64_t {t} = {if op == "prod" || op == "lcm" then "1ULL" else "0ULL"};"
    emitC s!"{ind}if ({l} {if incl then "<=" else "<"} {h}) \{"
    emitC s!"{ind}  uint64_t {v} = {l};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExpr sym ind2 filt
    emitC s!"{ind2}if ({f} != 0ULL) \{"
    let ind3 := ind2 ++ "  "
    if op == "count" then
      emitC s!"{ind3}if (lm2_add({t}, 1ULL, &{t})) return LM2_OVERFLOW;"
    else if op == "max" then
      let b ← cExpr sym ind3 body
      emitC s!"{ind3}if ({b} > {t}) {t} = {b};"
    else
      let b ← cExpr sym ind3 body
      emitC s!"{ind3}if (lm2_{if op == "prod" then "mul" else if op == "lcm" then "lcm" else "add"}({t}, {b}, &{t})) return LM2_OVERFLOW;"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {h}" else s!"{v} + 1ULL == {h}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    return t
  | .iter id acc lo hi incl filt init body => do
    let l ← cExpr sym ind lo
    let h ← cExpr sym ind hi
    let i0 ← cExpr sym ind init
    let v := s!"v{id}"
    let a := s!"v{acc}"
    let t ← freshC
    -- own block: the accumulator name is per iter node, which may be emitted more than once
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}\{ uint64_t {a} = {i0};"
    emitC s!"{ind}if ({l} {if incl then "<=" else "<"} {h}) \{"
    emitC s!"{ind}  uint64_t {v} = {l};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExpr sym ind2 filt
    emitC s!"{ind2}if ({f} != 0ULL) \{"
    let b ← cExpr sym (ind2 ++ "  ") body
    emitC s!"{ind2}  {a} = {b};"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {h}" else s!"{v} + 1ULL == {h}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    emitC s!"{ind}{t} = {a}; }"
    return t
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← cExpr sym ind a)
    let t ← freshC
    emitC s!"{ind}uint64_t {t};"
    emitC s!"{ind}if ({sym f}({", ".intercalate (vs.toList ++ [s!"&{t}"])}) != LM2_OK) return LM2_OVERFLOW;"
    return t

/-- ℤ subterms as checked `int64_t` (an intermediate outside int64 is reported as overflow).
An ill-typed node becomes `#error`, so the build fails closed. -/
partial def cExprI (sym : Name → String) (ind : String) : E → CGM String
  | .prim "qnum" [_] => do
    let t ← freshC
    emitC s!"{ind}int64_t {t} = 0; if (1) return LM2_OVERFLOW;"
    return t
  | .prim "ofnat" [x] => do
    let v ← cExpr sym ind x
    let t ← freshC
    emitC s!"{ind}int64_t {t};"
    emitC s!"{ind}if (lm2_ofnat({v}, &{t})) return LM2_OVERFLOW;"
    return t
  | .prim "ineg" [x] => do
    let v ← cExprI sym ind x
    let t ← freshC
    emitC s!"{ind}int64_t {t};"
    emitC s!"{ind}if (lm2_ineg({v}, &{t})) return LM2_OVERFLOW;"
    return t
  | .prim "isign" [x] => do
    let v ← cExprI sym ind x
    let t ← freshC
    emitC s!"{ind}int64_t {t} = lm2_isign({v});"
    return t
  | .bin op a b => do
    let x ← cExprI sym ind a
    let y ← if op == "ipow" then cExpr sym ind b else cExprI sym ind b
    let t ← freshC
    emitC s!"{ind}int64_t {t};"
    emitC s!"{ind}if (lm2_{op}({x}, {y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .ite c th el => do
    let x ← cExpr sym ind c
    let t ← freshC
    emitC s!"{ind}int64_t {t};"
    emitC s!"{ind}if ({x} != 0ULL) \{"
    let r1 ← cExprI sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExprI sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← cExpr sym ind lo
    let h ← cExpr sym ind hi
    let t ← freshC
    let v := s!"v{id}"
    emitC s!"{ind}int64_t {t} = {if op == "iprod" then "1" else "0"};"
    emitC s!"{ind}if ({l} {if incl then "<=" else "<"} {h}) \{"
    emitC s!"{ind}  uint64_t {v} = {l};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExpr sym ind2 filt
    emitC s!"{ind2}if ({f} != 0ULL) \{"
    let ind3 := ind2 ++ "  "
    let b ← cExprI sym ind3 body
    emitC s!"{ind3}if (lm2_{if op == "iprod" then "imul" else "iadd"}({t}, {b}, &{t})) return LM2_OVERFLOW;"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {h}" else s!"{v} + 1ULL == {h}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    return t
  | _ => do
    emitC "#error \"ill-typed MathIR integer node\""
    return "0"
end

def cParams (arity : Nat) : String :=
  ", ".intercalate ((List.range arity).map (s!"uint64_t a{·}") ++ ["uint64_t *out"])

def cFunction (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : CGM Unit := do
    emitC "  if (out == 0) return LM2_ERR_NULL;"
    match d with
    | .direct _ e =>
      let r ← cExpr sym "  " e
      emitC s!"  *out = {r};"
    | .recur _ j bases step =>
      let K := bases.length
      emitC s!"  uint64_t i;"
      for h : c in [0:K] do
        let r ← cExpr sym "  " bases[c]!
        emitC s!"  uint64_t w{c} = {r};"
      for c in List.range K do
        emitC s!"  if (a{j} == {c}ULL) \{ *out = w{c}; return LM2_OK; }"
      emitC "  for (i = 0ULL; ; i++) {"
      let r ← cExpr sym "    " step
      emitC s!"    uint64_t nv = {r};"
      for c in List.range (K - 1) do
        emitC s!"    w{c} = w{c + 1};"
      emitC s!"    w{K - 1} = nv;"
      emitC s!"    if (i == a{j} - {K}ULL) break;"
      emitC "  }"
      emitC s!"  *out = w{K - 1};"
    emitC "  return LM2_OK;"
  let st := (body.run {}).2
  s!"/* Lean: {n} (fast path: checked 64-bit) */\nstatic int32_t {sym n}_fast({cParams d.arity}) \{\n" ++ "\n".intercalate st.lines.toList ++ "\n}\n"

/-! ## C wide fallback (exact multi-precision, lm2_wide.h)

The public C function runs the fast 64-bit path; only if that reports overflow is the same IR
re-evaluated with exact `lm2w` / `lm2wi` intermediates, and the result returned iff it fits. -/

def cWideNat : String → String
  | "prime" => "prime" | op => op

def cCond (x : String) : String := s!"!lm2w_iszero(&{x})"

mutual
partial def cExprW (sym : Name → String) (ind : String) : E → CGM String
  | .lit n => do
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, {n}ULL);"
    return t
  | .arg i => pure s!"(*a{i})"
  | .idx => do
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, i);"
    return t
  | .prev j => pure s!"w{j}"
  | .lvar id => do
    if id ≥ accBase then return s!"v{id}"          -- accumulator: already wide
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, v{id});"
    return t
  | .bin op a b => do
    if op.startsWith "i" then emitC "#error \"ill-typed MathIR: integer operation in a natural-number position\""
    let x ← cExprW sym ind a
    let y ← cExprW sym ind b
    let t ← freshC
    emitC s!"{ind}lm2w {t};"
    emitC s!"{ind}if (lm2w_{op}(&{x}, &{y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .prim op as => do
    if op == "qden" then
      let x ← cExprWQ sym ind (as.headD default)
      let t ← freshC
      emitC s!"{ind}lm2w {t}; lm2wq_den(&{x}, &{t});"
      return t
    if op == "tonat" || op == "natabs" then
      let x ← cExprWI sym ind (as.headD default)
      let t ← freshC
      emitC s!"{ind}lm2w {t}; lm2wi_{op}(&{x}, &{t});"
      return t
    if op ∈ ["ofnat", "ineg", "isign"] then emitC "#error \"ill-typed MathIR: integer operation in a natural-number position\""
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← cExprW sym ind a)
    let t ← freshC
    emitC s!"{ind}lm2w {t};"
    emitC s!"{ind}if (lm2w_{cWideNat op}({", ".intercalate (vs.toList.map (s!"&{·}") ++ [s!"&{t}"])})) return LM2_OVERFLOW;"
    return t
  | .cmp k a b => do
    let ints := k.startsWith "i"
    let x ← if ints then cExprWI sym ind a else cExprW sym ind a
    let y ← if ints then cExprWI sym ind b else cExprW sym ind b
    let t ← freshC
    let rel := match k with | "lt" | "ilt" => "<" | "le" | "ile" => "<=" | _ => "=="
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, ({if ints then "lm2wi_cmp" else "lm2w_cmp"}(&{x}, &{y}) {rel} 0) ? 1u : 0u);"
    return t
  | .not a => do
    let x ← cExprW sym ind a
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, lm2w_iszero(&{x}) ? 1u : 0u);"
    return t
  | .and a b => do
    let x ← cExprW sym ind a
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, 0u);"
    emitC s!"{ind}if ({cCond x}) \{"
    let y ← cExprW sym (ind ++ "  ") b
    emitC s!"{ind}  lm2w_set(&{t}, lm2w_iszero(&{y}) ? 0u : 1u);"
    emitC s!"{ind}}"
    return t
  | .or a b => do
    let x ← cExprW sym ind a
    let t ← freshC
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, 1u);"
    emitC s!"{ind}if (lm2w_iszero(&{x})) \{"
    let y ← cExprW sym (ind ++ "  ") b
    emitC s!"{ind}  lm2w_set(&{t}, lm2w_iszero(&{y}) ? 0u : 1u);"
    emitC s!"{ind}}"
    return t
  | .ite c th el => do
    let x ← cExprW sym ind c
    let t ← freshC
    emitC s!"{ind}lm2w {t};"
    emitC s!"{ind}if ({cCond x}) \{"
    let r1 ← cExprW sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExprW sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .fold op id lo hi incl filt body => do
    if op.startsWith "i" then emitC "#error \"ill-typed MathIR: integer fold in a natural-number position\""
    let l ← cExprW sym ind lo
    let h ← cExprW sym ind hi
    let lb ← freshC
    let hb ← freshC
    let t ← freshC
    let v := s!"v{id}"
    -- loop bounds beyond 64 bits would never finish within any budget: fail (sound)
    emitC s!"{ind}uint64_t {lb}, {hb};"
    emitC s!"{ind}if (lm2w_get(&{l}, &{lb}) || lm2w_get(&{h}, &{hb})) return LM2_OVERFLOW;"
    emitC s!"{ind}lm2w {t}; lm2w_set(&{t}, {if op == "prod" || op == "lcm" then "1u" else "0u"});"
    emitC s!"{ind}if ({lb} {if incl then "<=" else "<"} {hb}) \{"
    emitC s!"{ind}  uint64_t {v} = {lb};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExprW sym ind2 filt
    emitC s!"{ind2}if ({cCond f}) \{"
    let ind3 := ind2 ++ "  "
    if op == "count" then
      emitC s!"{ind3}lm2w one; lm2w_set(&one, 1u);"
      emitC s!"{ind3}if (lm2w_add(&{t}, &one, &{t})) return LM2_OVERFLOW;"
    else if op == "max" then
      let b ← cExprW sym ind3 body
      emitC s!"{ind3}if (lm2w_cmp(&{b}, &{t}) > 0) {t} = {b};"
    else
      let b ← cExprW sym ind3 body
      emitC s!"{ind3}if (lm2w_{if op == "prod" then "mul" else if op == "lcm" then "lcm" else "add"}(&{t}, &{b}, &{t})) return LM2_OVERFLOW;"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {hb}" else s!"{v} + 1ULL == {hb}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    return t
  | .iter id acc lo hi incl filt init body => do
    let l ← cExprW sym ind lo
    let h ← cExprW sym ind hi
    let i0 ← cExprW sym ind init
    let lb ← freshC
    let hb ← freshC
    let v := s!"v{id}"
    let a := s!"v{acc}"
    emitC s!"{ind}uint64_t {lb}, {hb};"
    emitC s!"{ind}if (lm2w_get(&{l}, &{lb}) || lm2w_get(&{h}, &{hb})) return LM2_OVERFLOW;"
    let t ← freshC
    emitC s!"{ind}lm2w {t};"
    emitC s!"{ind}\{ lm2w {a}; {a} = {i0};"
    emitC s!"{ind}if ({lb} {if incl then "<=" else "<"} {hb}) \{"
    emitC s!"{ind}  uint64_t {v} = {lb};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExprW sym ind2 filt
    emitC s!"{ind2}if ({cCond f}) \{"
    let b ← cExprW sym (ind2 ++ "  ") body
    emitC s!"{ind2}  {a} = {b};"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {hb}" else s!"{v} + 1ULL == {hb}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    emitC s!"{ind}{t} = {a}; }"
    return t
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← cExprW sym ind a)
    let t ← freshC
    emitC s!"{ind}lm2w {t};"
    emitC s!"{ind}if ({sym f}_w({", ".intercalate (vs.toList.map (s!"&{·}") ++ [s!"&{t}"])}) != LM2_OK) return LM2_OVERFLOW;"
    return t

partial def cExprWI (sym : Name → String) (ind : String) : E → CGM String
  | .prim "qnum" [x] => do
    let v ← cExprWQ sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wi {t}; lm2wq_num(&{v}, &{t});"
    return t
  | .prim "ofnat" [x] => do
    let v ← cExprW sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wi {t}; lm2wi_ofnat(&{v}, &{t});"
    return t
  | .prim "ineg" [x] => do
    let v ← cExprWI sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wi {t}; lm2wi_neg(&{v}, &{t});"
    return t
  | .prim "isign" [x] => do
    let v ← cExprWI sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wi {t}; lm2wi_sign(&{v}, &{t});"
    return t
  | .bin op a b => do
    let x ← cExprWI sym ind a
    let y ← if op == "ipow" then cExprW sym ind b else cExprWI sym ind b
    let t ← freshC
    let fnm := match op with | "iadd" => "add" | "isub" => "sub" | "imul" => "mul" | _ => "pow"
    emitC s!"{ind}lm2wi {t};"
    emitC s!"{ind}if (lm2wi_{fnm}(&{x}, &{y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .ite c th el => do
    let x ← cExprW sym ind c
    let t ← freshC
    emitC s!"{ind}lm2wi {t};"
    emitC s!"{ind}if ({cCond x}) \{"
    let r1 ← cExprWI sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExprWI sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← cExprW sym ind lo
    let h ← cExprW sym ind hi
    let lb ← freshC
    let hb ← freshC
    let t ← freshC
    let v := s!"v{id}"
    emitC s!"{ind}uint64_t {lb}, {hb};"
    emitC s!"{ind}if (lm2w_get(&{l}, &{lb}) || lm2w_get(&{h}, &{hb})) return LM2_OVERFLOW;"
    emitC s!"{ind}lm2wi {t}; {t}.neg = 0; lm2w_set(&{t}.m, {if op == "iprod" then "1u" else "0u"});"
    emitC s!"{ind}if ({lb} {if incl then "<=" else "<"} {hb}) \{"
    emitC s!"{ind}  uint64_t {v} = {lb};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExprW sym ind2 filt
    emitC s!"{ind2}if ({cCond f}) \{"
    let ind3 := ind2 ++ "  "
    let b ← cExprWI sym ind3 body
    emitC s!"{ind3}if (lm2wi_{if op == "iprod" then "mul" else "add"}(&{t}, &{b}, &{t})) return LM2_OVERFLOW;"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {hb}" else s!"{v} + 1ULL == {hb}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    return t
  | _ => do
    emitC "#error \"ill-typed MathIR integer node\""
    return "0"

partial def cExprWQ (sym : Name → String) (ind : String) : E → CGM String
  | .prim "qofnat" [x] => do
    let v ← cExprW sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wq {t}; lm2wq_ofnat(&{v}, &{t});"
    return t
  | .prim "qofint" [x] => do
    let v ← cExprWI sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wq {t}; lm2wq_ofint(&{v}, &{t});"
    return t
  | .prim "qneg" [x] => do
    let v ← cExprWQ sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wq {t}; lm2wq_neg(&{v}, &{t});"
    return t
  | .prim "qinv" [x] => do
    let v ← cExprWQ sym ind x
    let t ← freshC
    emitC s!"{ind}lm2wq {t}; lm2wq_inv(&{v}, &{t});"
    return t
  | .bin op a b => do
    let x ← cExprWQ sym ind a
    let y ← if op == "qpow" then cExprW sym ind b else cExprWQ sym ind b
    let t ← freshC
    let fnm := match op with | "qadd" => "add" | "qsub" => "sub" | "qmul" => "mul" | "qdiv" => "div" | _ => "pow"
    emitC s!"{ind}lm2wq {t};"
    emitC s!"{ind}if (lm2wq_{fnm}(&{x}, &{y}, &{t})) return LM2_OVERFLOW;"
    return t
  | .ite c th el => do
    let x ← cExprW sym ind c
    let t ← freshC
    emitC s!"{ind}lm2wq {t};"
    emitC s!"{ind}if ({cCond x}) \{"
    let r1 ← cExprWQ sym (ind ++ "  ") th
    emitC s!"{ind}  {t} = {r1};"
    emitC s!"{ind}} else \{"
    let r2 ← cExprWQ sym (ind ++ "  ") el
    emitC s!"{ind}  {t} = {r2};"
    emitC s!"{ind}}"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← cExprW sym ind lo
    let h ← cExprW sym ind hi
    let lb ← freshC
    let hb ← freshC
    let t ← freshC
    let z ← freshC
    let v := s!"v{id}"
    emitC s!"{ind}uint64_t {lb}, {hb};"
    emitC s!"{ind}if (lm2w_get(&{l}, &{lb}) || lm2w_get(&{h}, &{hb})) return LM2_OVERFLOW;"
    emitC s!"{ind}lm2w {z}; lm2w_set(&{z}, {if op == "qprod" then "1u" else "0u"});"
    emitC s!"{ind}lm2wq {t}; lm2wq_ofnat(&{z}, &{t});"
    emitC s!"{ind}if ({lb} {if incl then "<=" else "<"} {hb}) \{"
    emitC s!"{ind}  uint64_t {v} = {lb};"
    emitC s!"{ind}  for (;;) \{"
    let ind2 := ind ++ "    "
    let f ← cExprW sym ind2 filt
    emitC s!"{ind2}if ({cCond f}) \{"
    let ind3 := ind2 ++ "  "
    let b ← cExprWQ sym ind3 body
    emitC s!"{ind3}if (lm2wq_{if op == "qprod" then "mul" else "add"}(&{t}, &{b}, &{t})) return LM2_OVERFLOW;"
    emitC s!"{ind2}}"
    emitC s!"{ind2}if ({if incl then s!"{v} == {hb}" else s!"{v} + 1ULL == {hb}"}) break;"
    emitC s!"{ind2}{v}++;"
    emitC s!"{ind}  }"
    emitC s!"{ind}}"
    return t
  | _ => do
    emitC "#error \"ill-typed MathIR rational node\""
    return "0"
end

def cParamsW (arity : Nat) : String :=
  ", ".intercalate ((List.range arity).map (s!"const lm2w *a{·}") ++ ["lm2w *out"])

def cFunctionW (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : CGM Unit := do
    match d with
    | .direct _ e =>
      let r ← cExprW sym "  " e
      emitC s!"  *out = {r};"
    | .recur _ j bases step =>
      let K := bases.length
      emitC "  uint64_t i, nrec;"
      emitC s!"  if (lm2w_get(a{j}, &nrec)) return LM2_OVERFLOW;"
      for h : c in [0:K] do
        let r ← cExprW sym "  " bases[c]!
        emitC s!"  lm2w w{c}; w{c} = {r};"
      for c in List.range K do
        emitC s!"  if (nrec == {c}ULL) \{ *out = w{c}; return LM2_OK; }"
      emitC "  for (i = 0ULL; ; i++) {"
      let r ← cExprW sym "    " step
      emitC s!"    lm2w nv = {r};"
      for c in List.range (K - 1) do
        emitC s!"    w{c} = w{c + 1};"
      emitC s!"    w{K - 1} = nv;"
      emitC s!"    if (i == nrec - {K}ULL) break;"
      emitC "  }"
      emitC s!"  *out = w{K - 1};"
    emitC "  return LM2_OK;"
  let st := (body.run {}).2
  s!"/* Lean: {n} (wide fallback: exact, lm2_wide.h) */\nstatic int32_t {sym n}_w({cParamsW d.arity}) \{\n" ++ "\n".intercalate st.lines.toList ++ "\n}\n"

/-- Public entry: fast path; on overflow, exact recomputation; the result is returned iff it fits. -/
def cWrapper (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let ks := List.range d.arity
  let decl := ", ".intercalate (ks.map (s!"A{·}") ++ ["R"])
  let sets := String.join (ks.map fun k => s!"  lm2w_set(&A{k}, a{k});\n")
  let fastArgs := ", ".intercalate (ks.map (s!"a{·}") ++ ["out"])
  let wideArgs := ", ".intercalate (ks.map (s!"&A{·}") ++ ["&R"])
  s!"int32_t {sym n}({cParams d.arity}) \{\n  int32_t s; uint64_t v; lm2w {decl};\n  if (out == 0) return LM2_ERR_NULL;\n" ++
  s!"  s = {sym n}_fast({fastArgs});\n  if (s != LM2_OVERFLOW) return s;\n" ++ sets ++
  s!"  if ({sym n}_w({wideArgs}) != LM2_OK) return LM2_OVERFLOW;\n  if (lm2w_get(&R, &v)) return LM2_OVERFLOW;\n  *out = v; return LM2_OK;\n}\n"

/-! ## Modula-2 emission (native; checked operations via LM2Nat) -/

structure MG where
  lines : Array String := #[]
  vars  : Array String := #[]     -- LONGCARD
  ivars : Array String := #[]     -- LONGINT (ℤ subterms)
  wvars : Array String := #[]     -- LM2Wide.Wide (wide fallback)
  wivars : Array String := #[]    -- LM2Wide.WInt (wide fallback, ℤ subterms)
  wqvars : Array String := #[]    -- LM2Wide.WRat (wide fallback, ℚ subterms)
  tmp   : Nat := 0

abbrev MGM := StateM MG

def emitM (l : String) : MGM Unit := modify fun s => { s with lines := s.lines.push l }
def freshM : MGM String := modifyGet fun s => (s!"t{s.tmp}", { s with tmp := s.tmp + 1, vars := s.vars.push s!"t{s.tmp}" })
def freshMI : MGM String := modifyGet fun s => (s!"z{s.tmp}", { s with tmp := s.tmp + 1, ivars := s.ivars.push s!"z{s.tmp}" })
def freshMW : MGM String := modifyGet fun s => (s!"x{s.tmp}", { s with tmp := s.tmp + 1, wvars := s.wvars.push s!"x{s.tmp}" })
def freshMWI : MGM String := modifyGet fun s => (s!"y{s.tmp}", { s with tmp := s.tmp + 1, wivars := s.wivars.push s!"y{s.tmp}" })
def freshMWQ : MGM String := modifyGet fun s => (s!"q{s.tmp}", { s with tmp := s.tmp + 1, wqvars := s.wqvars.push s!"q{s.tmp}" })
def declMW (v : String) : MGM Unit := modify fun s => if s.wvars.contains v then s else { s with wvars := s.wvars.push v }
def declM (v : String) : MGM Unit := modify fun s => if s.vars.contains v then s else { s with vars := s.vars.push v }

def m2Bin : String → String
  | "add" => "Add" | "mul" => "Mul" | "sub" => "Sub" | "div" => "Div" | "mod" => "Mod" | _ => "Pow"

def m2Prim : String → String
  | "min" => "Min" | "max" => "Max" | "gcd" => "Gcd" | "lcm" => "Lcm" | "fact" => "Fact"
  | "choose" => "Choose" | "sqrt" => "Sqrt" | "minfac" => "MinFac" | "prime" => "IsPrime"
  | "fib" => "Fib" | "log" => "Log" | "log2" => "Log2" | "padic" => "PadicVal" | "bigomega" => "BigOmega"
  | "digsum" => "DigSum" | "diglen" => "DigLen" | "digrev" => "DigRev" | "xor" => "Xor" | _ => "Dvd"

mutual
partial def mExpr (sym : Name → String) (ind : String) : E → MGM String
  | .lit n => pure (toString n)
  | .arg i => pure s!"a{i}"
  | .idx => pure "i"
  | .prev j => pure s!"w{j}"
  | .lvar id => do declM s!"v{id}"; pure s!"v{id}"
  | .bin op a b => do
    let x ← mExpr sym ind a
    let y ← mExpr sym ind b
    let t ← freshM
    emitM s!"{ind}IF LM2Nat.{m2Bin op}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim op as => do
    if op == "qden" then
      let t ← freshM
      emitM s!"{ind}{t} := 0; IF TRUE THEN RETURN Overflow END;   (* ℚ: exact wide path only *)"
      return t
    if op == "tonat" || op == "natabs" then
      let x ← mExprI sym ind (as.headD default)
      let t ← freshM
      emitM s!"{ind}{t} := LM2Nat.{if op == "tonat" then "ToNat" else "NatAbs"}({x});"
      return t
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← mExpr sym ind a)
    let t ← freshM
    let callArgs := ", ".intercalate vs.toList
    if op ∈ cPrimOverflowing then
      emitM s!"{ind}IF LM2Nat.{m2Prim op}({callArgs}, {t}) THEN RETURN Overflow END;"
    else
      emitM s!"{ind}{t} := LM2Nat.{m2Prim op}({callArgs});"
    return t
  | .cmp k a b => do
    let ints := k.startsWith "i"
    let x ← if ints then mExprI sym ind a else mExpr sym ind a
    let y ← if ints then mExprI sym ind b else mExpr sym ind b
    let t ← freshM
    let op := match k with | "lt" | "ilt" => "<" | "le" | "ile" => "<=" | _ => "="
    emitM s!"{ind}IF {x} {op} {y} THEN {t} := 1 ELSE {t} := 0 END;"
    return t
  | .not a => do
    let x ← mExpr sym ind a
    let t ← freshM
    emitM s!"{ind}IF {x} = 0 THEN {t} := 1 ELSE {t} := 0 END;"
    return t
  | .and a b => do
    let x ← mExpr sym ind a
    let t ← freshM
    emitM s!"{ind}{t} := 0;"
    emitM s!"{ind}IF {x} # 0 THEN"
    let y ← mExpr sym (ind ++ "  ") b
    emitM s!"{ind}  IF {y} # 0 THEN {t} := 1 END"
    emitM s!"{ind}END;"
    return t
  | .or a b => do
    let x ← mExpr sym ind a
    let t ← freshM
    emitM s!"{ind}{t} := 1;"
    emitM s!"{ind}IF {x} = 0 THEN"
    let y ← mExpr sym (ind ++ "  ") b
    emitM s!"{ind}  IF {y} = 0 THEN {t} := 0 END"
    emitM s!"{ind}END;"
    return t
  | .ite c th el => do
    let x ← mExpr sym ind c
    let t ← freshM
    emitM s!"{ind}IF {x} # 0 THEN"
    let r1 ← mExpr sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExpr sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← mExpr sym ind lo
    let h ← mExpr sym ind hi
    let t ← freshM
    let v := s!"v{id}"
    declM v
    emitM s!"{ind}{t} := {if op == "prod" || op == "lcm" then "1" else "0"};"
    emitM s!"{ind}IF {l} {if incl then "<=" else "<"} {h} THEN"
    emitM s!"{ind}  {v} := {l};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExpr sym ind2 filt
    emitM s!"{ind2}IF {f} # 0 THEN"
    let ind3 := ind2 ++ "  "
    if op == "count" then
      emitM s!"{ind3}IF LM2Nat.Add({t}, 1, {t}) THEN RETURN Overflow END"
    else if op == "max" then
      let b ← mExpr sym ind3 body
      emitM s!"{ind3}IF {b} > {t} THEN {t} := {b} END"
    else
      let b ← mExpr sym ind3 body
      emitM s!"{ind3}IF LM2Nat.{if op == "prod" then "Mul" else if op == "lcm" then "Lcm" else "Add"}({t}, {b}, {t}) THEN RETURN Overflow END"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {h}" else s!"{v} + 1 = {h}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return t
  | .iter id acc lo hi incl filt init body => do
    let l ← mExpr sym ind lo
    let h ← mExpr sym ind hi
    let i0 ← mExpr sym ind init
    let v := s!"v{id}"
    let a := s!"v{acc}"
    declM v; declM a
    emitM s!"{ind}{a} := {i0};"
    emitM s!"{ind}IF {l} {if incl then "<=" else "<"} {h} THEN"
    emitM s!"{ind}  {v} := {l};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExpr sym ind2 filt
    emitM s!"{ind2}IF {f} # 0 THEN"
    let b ← mExpr sym (ind2 ++ "  ") body
    emitM s!"{ind2}  {a} := {b}"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {h}" else s!"{v} + 1 = {h}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return a
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← mExpr sym ind a)
    let t ← freshM
    emitM s!"{ind}IF {sym f}({", ".intercalate (vs.toList ++ [t])}) # Ok THEN RETURN Overflow END;"
    return t

/-- ℤ subterms as checked LONGINT (see `cExprI`); an ill-typed node fails compilation. -/
partial def mExprI (sym : Name → String) (ind : String) : E → MGM String
  | .prim "qnum" [_] => do
    let t ← freshMI
    emitM s!"{ind}{t} := 0; IF TRUE THEN RETURN Overflow END;   (* ℚ: exact wide path only *)"
    return t
  | .prim "ofnat" [x] => do
    let v ← mExpr sym ind x
    let t ← freshMI
    emitM s!"{ind}IF LM2Nat.OfNat({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "ineg" [x] => do
    let v ← mExprI sym ind x
    let t ← freshMI
    emitM s!"{ind}IF LM2Nat.INeg({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "isign" [x] => do
    let v ← mExprI sym ind x
    let t ← freshMI
    emitM s!"{ind}{t} := LM2Nat.ISign({v});"
    return t
  | .bin op a b => do
    let x ← mExprI sym ind a
    let y ← if op == "ipow" then mExpr sym ind b else mExprI sym ind b
    let t ← freshMI
    let p := match op with | "iadd" => "IAdd" | "isub" => "ISub" | "imul" => "IMul" | _ => "IPow"
    emitM s!"{ind}IF LM2Nat.{p}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .ite c th el => do
    let x ← mExpr sym ind c
    let t ← freshMI
    emitM s!"{ind}IF {x} # 0 THEN"
    let r1 ← mExprI sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExprI sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← mExpr sym ind lo
    let h ← mExpr sym ind hi
    let t ← freshMI
    let v := s!"v{id}"
    declM v
    emitM s!"{ind}{t} := {if op == "iprod" then "1" else "0"};"
    emitM s!"{ind}IF {l} {if incl then "<=" else "<"} {h} THEN"
    emitM s!"{ind}  {v} := {l};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExpr sym ind2 filt
    emitM s!"{ind2}IF {f} # 0 THEN"
    let ind3 := ind2 ++ "  "
    let b ← mExprI sym ind3 body
    emitM s!"{ind3}IF LM2Nat.{if op == "iprod" then "IMul" else "IAdd"}({t}, {b}, {t}) THEN RETURN Overflow END"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {h}" else s!"{v} + 1 = {h}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return t
  | _ => do
    emitM "ILL-TYPED MathIR integer node (deliberate syntax error: fail closed)"
    return "0"
end

def mParams (arity : Nat) : String :=
  let as := ", ".intercalate ((List.range arity).map (s!"a{·}"))
  s!"{as}: LONGCARD; VAR out: LONGCARD"

def mVarDecl (st : MG) : String :=
  let one (vs : Array String) (ty : String) := if vs.isEmpty then "" else s!"  {", ".intercalate vs.toList}: {ty};\n"
  let all := one st.vars "LONGCARD" ++ one st.ivars "LONGINT" ++ one st.wvars "LM2Wide.Wide" ++ one st.wivars "LM2Wide.WInt" ++ one st.wqvars "LM2Wide.WRat"
  if all == "" then "" else "VAR\n" ++ all

def mProcedure (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : MGM Unit := do
    match d with
    | .direct _ e =>
      let r ← mExpr sym "  " e
      emitM s!"  out := {r};"
    | .recur _ j bases step =>
      let K := bases.length
      declM "i"; declM "nv"
      for h : c in [0:K] do
        declM s!"w{c}"
        let r ← mExpr sym "  " bases[c]!
        emitM s!"  w{c} := {r};"
      for c in List.range K do
        emitM s!"  IF a{j} = {c} THEN out := w{c}; RETURN Ok END;"
      emitM "  i := 0;"
      emitM "  LOOP"
      let r ← mExpr sym "    " step
      emitM s!"    nv := {r};"
      for c in List.range (K - 1) do
        emitM s!"    w{c} := w{c + 1};"
      emitM s!"    w{K - 1} := nv;"
      emitM s!"    IF i = a{j} - {K} THEN EXIT END;"
      emitM "    INC(i)"
      emitM "  END;"
      emitM s!"  out := w{K - 1};"
    emitM "  RETURN Ok"
  let st := (body.run {}).2
  s!"(* Lean: {n} (fast path: checked LONGCARD) *)\nPROCEDURE {sym n}Fast ({mParams d.arity}) : INTEGER;\n{mVarDecl st}BEGIN\n" ++
    "\n".intercalate st.lines.toList ++ s!"\nEND {sym n}Fast;\n"

/-! ## Modula-2 wide fallback (exact multi-precision, LM2Wide) -/

def m2Wide : String → String
  | "add" => "Add" | "mul" => "Mul" | "sub" => "Sub" | "div" => "Div" | "mod" => "Mod" | "pow" => "Pow"
  | "min" => "Min" | "max" => "Max" | "gcd" => "Gcd" | "lcm" => "Lcm" | "fact" => "Fact"
  | "choose" => "Choose" | "sqrt" => "Sqrt" | "minfac" => "MinFac" | "prime" => "Prime"
  | "bigomega" => "BigOmega" | "dvd" => "Dvd" | "fib" => "Fib" | "log" => "Log" | "log2" => "Log2"
  | "padic" => "Padic" | "digsum" => "DigSum" | "diglen" => "DigLen" | "digrev" => "DigRev"
  | "xor" => "Xor"
  | op => s!"ILLTYPED_{op}"

mutual
partial def mExprW (sym : Name → String) (ind : String) : E → MGM String
  | .lit n => do
    let t ← freshMW
    emitM s!"{ind}LM2Wide.Set({t}, {n});"
    return t
  | .arg i => pure s!"a{i}"
  | .idx => do
    let t ← freshMW
    emitM s!"{ind}LM2Wide.Set({t}, i);"
    return t
  | .prev j => do declMW s!"w{j}"; pure s!"w{j}"
  | .lvar id => do
    if id ≥ accBase then
      declMW s!"v{id}"; return s!"v{id}"            -- accumulator: already wide
    declM s!"v{id}"
    let t ← freshMW
    emitM s!"{ind}LM2Wide.Set({t}, v{id});"
    return t
  | .bin op a b => do
    let x ← mExprW sym ind a
    let y ← mExprW sym ind b
    let t ← freshMW
    emitM s!"{ind}IF LM2Wide.{m2Wide op}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim op as => do
    if op == "qden" then
      let x ← mExprWQ sym ind (as.headD default)
      let t ← freshMW
      emitM s!"{ind}IF LM2Wide.QDen({x}, {t}) THEN RETURN Overflow END;"
      return t
    if op == "tonat" || op == "natabs" then
      let x ← mExprWI sym ind (as.headD default)
      let t ← freshMW
      emitM s!"{ind}IF LM2Wide.{if op == "tonat" then "IToNat" else "INatAbs"}({x}, {t}) THEN RETURN Overflow END;"
      return t
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← mExprW sym ind a)
    let t ← freshMW
    emitM s!"{ind}IF LM2Wide.{m2Wide op}({", ".intercalate (vs.toList ++ [t])}) THEN RETURN Overflow END;"
    return t
  | .cmp k a b => do
    let ints := k.startsWith "i"
    let x ← if ints then mExprWI sym ind a else mExprW sym ind a
    let y ← if ints then mExprWI sym ind b else mExprW sym ind b
    let t ← freshMW
    let rel := match k with | "lt" | "ilt" => "<" | "le" | "ile" => "<=" | _ => "="
    emitM s!"{ind}IF LM2Wide.{if ints then "ICmp" else "Cmp"}({x}, {y}) {rel} 0 THEN LM2Wide.Set({t}, 1) ELSE LM2Wide.Set({t}, 0) END;"
    return t
  | .not a => do
    let x ← mExprW sym ind a
    let t ← freshMW
    emitM s!"{ind}IF LM2Wide.IsZero({x}) THEN LM2Wide.Set({t}, 1) ELSE LM2Wide.Set({t}, 0) END;"
    return t
  | .and a b => do
    let x ← mExprW sym ind a
    let t ← freshMW
    emitM s!"{ind}LM2Wide.Set({t}, 0);"
    emitM s!"{ind}IF NOT LM2Wide.IsZero({x}) THEN"
    let y ← mExprW sym (ind ++ "  ") b
    emitM s!"{ind}  IF NOT LM2Wide.IsZero({y}) THEN LM2Wide.Set({t}, 1) END"
    emitM s!"{ind}END;"
    return t
  | .or a b => do
    let x ← mExprW sym ind a
    let t ← freshMW
    emitM s!"{ind}LM2Wide.Set({t}, 1);"
    emitM s!"{ind}IF LM2Wide.IsZero({x}) THEN"
    let y ← mExprW sym (ind ++ "  ") b
    emitM s!"{ind}  IF LM2Wide.IsZero({y}) THEN LM2Wide.Set({t}, 0) END"
    emitM s!"{ind}END;"
    return t
  | .ite c th el => do
    let x ← mExprW sym ind c
    let t ← freshMW
    emitM s!"{ind}IF NOT LM2Wide.IsZero({x}) THEN"
    let r1 ← mExprW sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExprW sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← mExprW sym ind lo
    let h ← mExprW sym ind hi
    let lb ← freshM
    let hb ← freshM
    let t ← freshMW
    let one ← freshMW
    let v := s!"v{id}"
    declM v
    emitM s!"{ind}IF LM2Wide.Get({l}, {lb}) OR LM2Wide.Get({h}, {hb}) THEN RETURN Overflow END;"
    emitM s!"{ind}LM2Wide.Set({t}, {if op == "prod" || op == "lcm" then "1" else "0"}); LM2Wide.Set({one}, 1);"
    emitM s!"{ind}IF {lb} {if incl then "<=" else "<"} {hb} THEN"
    emitM s!"{ind}  {v} := {lb};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExprW sym ind2 filt
    emitM s!"{ind2}IF NOT LM2Wide.IsZero({f}) THEN"
    let ind3 := ind2 ++ "  "
    if op == "count" then
      emitM s!"{ind3}IF LM2Wide.Add({t}, {one}, {t}) THEN RETURN Overflow END"
    else if op == "max" then
      let b ← mExprW sym ind3 body
      emitM s!"{ind3}IF LM2Wide.Cmp({b}, {t}) > 0 THEN {t} := {b} END"
    else if op == "sum" || op == "prod" || op == "lcm" then
      let b ← mExprW sym ind3 body
      emitM s!"{ind3}IF LM2Wide.{if op == "prod" then "Mul" else if op == "lcm" then "Lcm" else "Add"}({t}, {b}, {t}) THEN RETURN Overflow END"
    else
      emitM "ILL-TYPED MathIR integer fold (deliberate syntax error: fail closed)"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {hb}" else s!"{v} + 1 = {hb}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return t
  | .iter id acc lo hi incl filt init body => do
    let l ← mExprW sym ind lo
    let h ← mExprW sym ind hi
    let i0 ← mExprW sym ind init
    let lb ← freshM
    let hb ← freshM
    let v := s!"v{id}"
    let a := s!"v{acc}"
    declM v; declMW a
    emitM s!"{ind}IF LM2Wide.Get({l}, {lb}) OR LM2Wide.Get({h}, {hb}) THEN RETURN Overflow END;"
    emitM s!"{ind}{a} := {i0};"
    emitM s!"{ind}IF {lb} {if incl then "<=" else "<"} {hb} THEN"
    emitM s!"{ind}  {v} := {lb};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExprW sym ind2 filt
    emitM s!"{ind2}IF NOT LM2Wide.IsZero({f}) THEN"
    let b ← mExprW sym (ind2 ++ "  ") body
    emitM s!"{ind2}  {a} := {b}"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {hb}" else s!"{v} + 1 = {hb}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return a
  | .call f as => do
    let mut vs : Array String := #[]
    for a in as do vs := vs.push (← mExprW sym ind a)
    let t ← freshMW
    emitM s!"{ind}IF {sym f}W({", ".intercalate (vs.toList ++ [t])}) # Ok THEN RETURN Overflow END;"
    return t

partial def mExprWI (sym : Name → String) (ind : String) : E → MGM String
  | .prim "qnum" [x] => do
    let v ← mExprWQ sym ind x
    let t ← freshMWI
    emitM s!"{ind}IF LM2Wide.QNum({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "ofnat" [x] => do
    let v ← mExprW sym ind x
    let t ← freshMWI
    emitM s!"{ind}IF LM2Wide.IOfNat({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "ineg" [x] => do
    let v ← mExprWI sym ind x
    let t ← freshMWI
    emitM s!"{ind}IF LM2Wide.INeg({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "isign" [x] => do
    let v ← mExprWI sym ind x
    let t ← freshMWI
    emitM s!"{ind}IF LM2Wide.ISign({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .bin op a b => do
    let x ← mExprWI sym ind a
    let y ← if op == "ipow" then mExprW sym ind b else mExprWI sym ind b
    let t ← freshMWI
    let p := match op with | "iadd" => "IAdd" | "isub" => "ISub" | "imul" => "IMul" | _ => "IPow"
    emitM s!"{ind}IF LM2Wide.{p}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .ite c th el => do
    let x ← mExprW sym ind c
    let t ← freshMWI
    emitM s!"{ind}IF NOT LM2Wide.IsZero({x}) THEN"
    let r1 ← mExprWI sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExprWI sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← mExprW sym ind lo
    let h ← mExprW sym ind hi
    let lb ← freshM
    let hb ← freshM
    let t ← freshMWI
    let v := s!"v{id}"
    declM v
    emitM s!"{ind}IF LM2Wide.Get({l}, {lb}) OR LM2Wide.Get({h}, {hb}) THEN RETURN Overflow END;"
    emitM s!"{ind}{t}.neg := FALSE; LM2Wide.Set({t}.m, {if op == "iprod" then "1" else "0"});"
    emitM s!"{ind}IF {lb} {if incl then "<=" else "<"} {hb} THEN"
    emitM s!"{ind}  {v} := {lb};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExprW sym ind2 filt
    emitM s!"{ind2}IF NOT LM2Wide.IsZero({f}) THEN"
    let ind3 := ind2 ++ "  "
    let b ← mExprWI sym ind3 body
    emitM s!"{ind3}IF LM2Wide.{if op == "iprod" then "IMul" else "IAdd"}({t}, {b}, {t}) THEN RETURN Overflow END"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {hb}" else s!"{v} + 1 = {hb}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return t
  | _ => do
    emitM "ILL-TYPED MathIR integer node (deliberate syntax error: fail closed)"
    return "0"

partial def mExprWQ (sym : Name → String) (ind : String) : E → MGM String
  | .prim "qofnat" [x] => do
    let v ← mExprW sym ind x
    let t ← freshMWQ
    emitM s!"{ind}IF LM2Wide.QOfNat({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "qofint" [x] => do
    let v ← mExprWI sym ind x
    let t ← freshMWQ
    emitM s!"{ind}IF LM2Wide.QOfInt({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "qneg" [x] => do
    let v ← mExprWQ sym ind x
    let t ← freshMWQ
    emitM s!"{ind}IF LM2Wide.QNeg({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .prim "qinv" [x] => do
    let v ← mExprWQ sym ind x
    let t ← freshMWQ
    emitM s!"{ind}IF LM2Wide.QInv({v}, {t}) THEN RETURN Overflow END;"
    return t
  | .bin op a b => do
    let x ← mExprWQ sym ind a
    let y ← if op == "qpow" then mExprW sym ind b else mExprWQ sym ind b
    let t ← freshMWQ
    let p := match op with | "qadd" => "QAdd" | "qsub" => "QSub" | "qmul" => "QMul" | "qdiv" => "QDiv" | _ => "QPow"
    emitM s!"{ind}IF LM2Wide.{p}({x}, {y}, {t}) THEN RETURN Overflow END;"
    return t
  | .ite c th el => do
    let x ← mExprW sym ind c
    let t ← freshMWQ
    emitM s!"{ind}IF NOT LM2Wide.IsZero({x}) THEN"
    let r1 ← mExprWQ sym (ind ++ "  ") th
    emitM s!"{ind}  {t} := {r1}"
    emitM s!"{ind}ELSE"
    let r2 ← mExprWQ sym (ind ++ "  ") el
    emitM s!"{ind}  {t} := {r2}"
    emitM s!"{ind}END;"
    return t
  | .fold op id lo hi incl filt body => do
    let l ← mExprW sym ind lo
    let h ← mExprW sym ind hi
    let lb ← freshM
    let hb ← freshM
    let t ← freshMWQ
    let z ← freshMW
    let v := s!"v{id}"
    declM v
    emitM s!"{ind}IF LM2Wide.Get({l}, {lb}) OR LM2Wide.Get({h}, {hb}) THEN RETURN Overflow END;"
    emitM s!"{ind}LM2Wide.Set({z}, {if op == "qprod" then "1" else "0"});"
    emitM s!"{ind}IF LM2Wide.QOfNat({z}, {t}) THEN RETURN Overflow END;"
    emitM s!"{ind}IF {lb} {if incl then "<=" else "<"} {hb} THEN"
    emitM s!"{ind}  {v} := {lb};"
    emitM s!"{ind}  LOOP"
    let ind2 := ind ++ "    "
    let f ← mExprW sym ind2 filt
    emitM s!"{ind2}IF NOT LM2Wide.IsZero({f}) THEN"
    let ind3 := ind2 ++ "  "
    let b ← mExprWQ sym ind3 body
    emitM s!"{ind3}IF LM2Wide.{if op == "qprod" then "QMul" else "QAdd"}({t}, {b}, {t}) THEN RETURN Overflow END"
    emitM s!"{ind2}END;"
    emitM s!"{ind2}IF {if incl then s!"{v} = {hb}" else s!"{v} + 1 = {hb}"} THEN EXIT END;"
    emitM s!"{ind2}INC({v})"
    emitM s!"{ind}  END"
    emitM s!"{ind}END;"
    return t
  | _ => do
    emitM "ILL-TYPED MathIR rational node (deliberate syntax error: fail closed)"
    return "0"
end

def mParamsW (arity : Nat) : String :=
  let as := ", ".intercalate ((List.range arity).map (s!"a{·}"))
  s!"VAR {as}: LM2Wide.Wide; VAR out: LM2Wide.Wide"

def mProcedureW (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let body : MGM Unit := do
    match d with
    | .direct _ e =>
      let r ← mExprW sym "  " e
      emitM s!"  out := {r};"
    | .recur _ j bases step =>
      let K := bases.length
      declM "i"; declM "nrec"; declMW "nv"
      emitM s!"  IF LM2Wide.Get(a{j}, nrec) THEN RETURN Overflow END;"
      for h : c in [0:K] do
        declMW s!"w{c}"
        let r ← mExprW sym "  " bases[c]!
        emitM s!"  w{c} := {r};"
      for c in List.range K do
        emitM s!"  IF nrec = {c} THEN out := w{c}; RETURN Ok END;"
      emitM "  i := 0;"
      emitM "  LOOP"
      let r ← mExprW sym "    " step
      emitM s!"    nv := {r};"
      for c in List.range (K - 1) do
        emitM s!"    w{c} := w{c + 1};"
      emitM s!"    w{K - 1} := nv;"
      emitM s!"    IF i = nrec - {K} THEN EXIT END;"
      emitM "    INC(i)"
      emitM "  END;"
      emitM s!"  out := w{K - 1};"
    emitM "  RETURN Ok"
  let st := (body.run {}).2
  s!"(* Lean: {n} (wide fallback: exact, LM2Wide) *)\nPROCEDURE {sym n}W ({mParamsW d.arity}) : INTEGER;\n{mVarDecl st}BEGIN\n" ++
    "\n".intercalate st.lines.toList ++ s!"\nEND {sym n}W;\n"

/-- Public entry: fast path; on overflow, exact recomputation; the result is returned iff it fits. -/
def mWrapper (sym : Name → String) (n : Name) (d : FnDef) : String :=
  let ks := List.range d.arity
  let wide := ", ".intercalate (ks.map (s!"A{·}") ++ ["R"])
  let sets := String.join (ks.map fun k => s!"  LM2Wide.Set(A{k}, a{k});\n")
  let fastArgs := ", ".intercalate (ks.map (s!"a{·}") ++ ["out"])
  let wideArgs := ", ".intercalate (ks.map (s!"A{·}") ++ ["R"])
  s!"PROCEDURE {sym n} ({mParams d.arity}) : INTEGER;\nVAR\n  s: INTEGER; v: LONGCARD;\n  {wide}: LM2Wide.Wide;\nBEGIN\n" ++
  s!"  s := {sym n}Fast({fastArgs});\n  IF s # Overflow THEN RETURN s END;\n" ++ sets ++
  s!"  IF {sym n}W({wideArgs}) # Ok THEN RETURN Overflow END;\n  IF LM2Wide.Get(R, v) THEN RETURN Overflow END;\n  out := v; RETURN Ok\nEND {sym n};\n"

/-- Lookback offsets `j` used by a step (as `prev j`), de-duplicated: Lean's compiler shares
identical calls within an expression, so each distinct `f (m + j)` is one call. -/
partial def E.prevs (e : E) : List Nat :=
  ((match e with | .prev j => [j] | _ => []) ++ e.children.flatMap E.prevs).eraseDups

/-- Size of the call tree of Lean's *compiled* evaluation of a lookback recursion at `n`
(naive tree recursion: cost(n) = 1 for n < K, else 1 + Σ_{j ∈ ds} cost(n - K + j)), saturating
just above `cap`. The generated code is linear; this only bounds the reference evaluation. -/
def naiveCost (K : Nat) (ds : List Nat) (n cap : Nat) : Nat := Id.run do
  let mut c : Array Nat := #[]
  for m in [0:n + 1] do
    if m < K then c := c.push 1
    else
      let v := ds.foldl (fun acc j => acc + c.getD (m - K + j) 0) 1
      c := c.push (min v (cap + 1))
  return c.getD n 0

/-! ## Budgeted IR interpreter (exact ℕ, aborts instead of exploding) -/

/-- Any intermediate above `2^maxBits`, more than `maxSteps` loop iterations / calls in total,
`choose` with n > 24 (Mathlib's `Nat.choose` is naive binary recursion at run time), or
primality / `minFac` above 2^20 aborts the evaluation (`none`). -/
structure Budget where
  maxBits    : Nat := 4096
  naiveCalls : Nat := 2000000   -- call-tree size of Lean's naive evaluation of lookback recursion
  steps   : Nat := 20000   -- the interpreter runs inside `#eval` (interpreted), so keep this modest

abbrev IRM := StateT Nat (Except String)   -- state: steps used

def tick (b : Budget) : IRM Unit := do
  let s ← get
  if s ≥ b.steps then throw "step budget"
  set (s + 1)

def chk (b : Budget) (v : Nat) : IRM Nat :=
  if v.log2 ≥ b.maxBits then throw "size budget" else pure v

def chkI (b : Budget) (v : Int) : IRM Int :=
  if v.natAbs.log2 ≥ b.maxBits then throw "size budget" else pure v

/-- Normalize a fraction (Lean's ℚ: lowest terms, positive denominator), with the size budget. -/
def qnorm (b : Budget) (n : Int) (d : Nat) : IRM (Int × Nat) := do
  if d == 0 then throw "ill-formed fraction"
  if n == 0 then return (0, 1)
  let g := Nat.gcd n.natAbs d
  let n' ← chkI b (n / Int.ofNat g)
  let d' ← chk b (d / g)
  return (n', d')

def b2n (p : Bool) : Nat := if p then 1 else 0

/-- Independent exact implementations for the interpreter (Lean core only; the fidelity check then
compares them against Mathlib's compiled definitions inside the corpus functions). -/
def factN (n : Nat) : Nat := Id.run do
  let mut a := 1
  for i in [2:n + 1] do a := a * i
  return a

/-- C(n, k) by the exact multiplicative formula; 0 if k > n. -/
def chooseN (n k : Nat) : Nat := Id.run do
  if k > n then return 0
  let k := min k (n - k)
  let mut c := 1
  for i in [1:k + 1] do c := c * (n - k + i) / i
  return c

/-- Mathlib's `Nat.digits` (little-endian): base 0 gives `[n]` (n > 0), base 1 gives n ones. -/
def digitsN (b n : Nat) : List Nat := Id.run do
  if n == 0 then return []
  if b == 0 then return [n]
  if b == 1 then return List.replicate n 1
  let mut out : Array Nat := #[]
  let mut m := n
  while m > 0 do
    out := out.push (m % b)
    m := m / b
  return out.toList

/-- `Nat.fib`: fib 0 = 0, fib 1 = 1. -/
def fibN (n : Nat) : Nat := Id.run do
  let mut x := 0
  let mut y := 1
  for _ in [0:n] do
    let z := x + y
    x := y
    y := z
  return x

/-- `Nat.ofDigits b L = L₀ + b * (L₁ + b * …)`. -/
def ofDigitsN (b : Nat) (L : List Nat) : Nat := L.foldr (fun h acc => h + b * acc) 0

/-- Floor logarithm, 0 for b ≤ 1 or n < b (Mathlib's `Nat.log`; `Nat.log2` is `logN 2`). -/
def logN (b n : Nat) : Nat := Id.run do
  if b ≤ 1 then return 0
  let mut k := 0
  let mut m := n
  while m ≥ b do
    m := m / b
    k := k + 1
  return k

/-- `padicValNat p n`: 0 for p ≤ 1 or n = 0, else the exponent of p in n. -/
def padicN (p n : Nat) : Nat := Id.run do
  if p ≤ 1 || n == 0 then return 0
  let mut k := 0
  let mut m := n
  while m % p == 0 do
    m := m / p
    k := k + 1
  return k

/-- Ω n = length of `Nat.primeFactorsList n` (0 for n ≤ 1). -/
def bigOmegaN (n : Nat) : Nat := Id.run do
  if n ≤ 1 then return 0
  let mut k := 0
  let mut m := n
  let mut d := 2
  while d * d ≤ m do
    while m % d == 0 do
      m := m / d
      k := k + 1
    d := d + 1
  if m > 1 then k := k + 1
  return k

/-- Mathlib's `Nat.minFac`: minFac 0 = 2, minFac 1 = 1, else the least prime factor. -/
def minFacN (n : Nat) : Nat := Id.run do
  if n == 0 then return 2
  if n == 1 then return 1
  if n % 2 == 0 then return 2
  let mut d := 3
  while d * d ≤ n do
    if n % d == 0 then return d
    d := d + 2
  return n


mutual
partial def evalE (b : Budget) (defs : Std.HashMap Name FnDef) (args : Array Nat) (i : Nat)
    (w : Array Nat) (lv : Std.HashMap Nat Nat) : E → IRM Nat
  | .lit n => pure n
  | .arg k => pure (args.getD k 0)
  | .idx => pure i
  | .prev j => pure (w.getD j 0)
  | .lvar id => pure (lv.getD id 0)
  | .bin op x y => do
    let a ← evalE b defs args i w lv x
    let c ← evalE b defs args i w lv y
    match op with
    | "add" => chk b (a + c)
    | "mul" => chk b (a * c)
    | "sub" => pure (a - c)
    | "div" => pure (a / c)
    | "mod" => pure (a % c)
    | _ =>
      -- Lean's runtime `Nat.pow` (lean_nat_pow, v4.33.1 src/runtime/object.cpp) calls
      -- lean_internal_panic — process exit 1 — for any exponent > UINT_MAX, whatever the base.
      -- The compiled corpus definition cannot be evaluated there, so neither may we: skip.
      if c > 4294967295 then throw "runtime limit: Nat.pow exponent > 2^32-1"
      else if a ≤ 1 || c == 0 then pure (a ^ c)
      else if c * (a.log2 + 1) > b.maxBits + 64 then throw "size budget"
      else chk b (a ^ c)
  | .prim op xs => do
    if op == "tonat" || op == "natabs" then
      let v ← evalI b defs args i w lv (xs.headD default)
      return (if op == "tonat" then v.toNat else v.natAbs)
    if op == "qden" then
      return (← evalQ b defs args i w lv (xs.headD default)).2
    let mut vs : Array Nat := #[]
    for x in xs do vs := vs.push (← evalE b defs args i w lv x)
    let a := vs.getD 0 0
    let c := vs.getD 1 0
    match op with
    | "min" => pure (min a c)
    | "max" => pure (max a c)
    | "gcd" => pure (Nat.gcd a c)
    | "lcm" => chk b (Nat.lcm a c)
    | "fact" => if a > 1000 then throw "size budget" else chk b (factN a)
    | "choose" => if a > 24 then throw "choose budget" else pure (chooseN a c)
    | "sqrt" => pure (Nat.sqrt a)
    | "minfac" => if a > 2 ^ 20 then throw "minFac budget" else pure (minFacN a)
    | "prime" => if a > 2 ^ 20 then throw "prime budget" else pure (b2n (a ≥ 2 && minFacN a == a))
    -- Mathlib's `Nat.fib` iterates n times; past fib 6000 the value exceeds 2^4096 anyway
    | "fib" => if a > 6000 then throw "size budget" else chk b (fibN a)
    | "xor" => pure (a ^^^ c)
    | "log" => pure (logN a c)
    | "log2" => pure (logN 2 a)
    | "padic" => pure (padicN a c)
    | "bigomega" => if a > 2 ^ 20 then throw "factor budget" else pure (bigOmegaN a)
    -- base 1 builds a list of n ones (in Lean's reference too)
    | "digsum" => if a == 1 && c > 2 ^ 16 then throw "digits budget" else pure (digitsN a c).sum
    | "diglen" => if a == 1 && c > 2 ^ 16 then throw "digits budget" else pure (digitsN a c).length
    | "digrev" => if a == 1 && c > 2 ^ 16 then throw "digits budget" else chk b (ofDigitsN a (digitsN a c).reverse)
    | _ => pure (b2n (if a == 0 then c == 0 else c % a == 0))   -- dvd
  | .cmp k x y => do
    if k.startsWith "i" then
      let a ← evalI b defs args i w lv x
      let c ← evalI b defs args i w lv y
      return b2n (match k with | "ilt" => decide (a < c) | "ile" => decide (a ≤ c) | _ => a == c)
    let a ← evalE b defs args i w lv x
    let c ← evalE b defs args i w lv y
    pure (b2n (match k with | "lt" => decide (a < c) | "le" => decide (a ≤ c) | _ => a == c))
  | .not x => do pure (b2n ((← evalE b defs args i w lv x) == 0))
  | .and x y => do
    if (← evalE b defs args i w lv x) == 0 then pure 0
    else pure (b2n ((← evalE b defs args i w lv y) != 0))
  | .or x y => do
    if (← evalE b defs args i w lv x) != 0 then pure 1
    else pure (b2n ((← evalE b defs args i w lv y) != 0))
  | .ite c t e => do
    if (← evalE b defs args i w lv c) != 0 then evalE b defs args i w lv t else evalE b defs args i w lv e
  | .fold op id lo hi incl filt body => do
    let l ← evalE b defs args i w lv lo
    let h ← evalE b defs args i w lv hi
    let stop := if incl then h + 1 else h
    let mut acc := if op == "prod" || op == "lcm" then 1 else 0
    let mut k := l
    while k < stop do
      tick b
      let lv' := lv.insert id k
      if (← evalE b defs args i w lv' filt) != 0 then
        if op == "count" then acc := acc + 1
        else
          let v ← evalE b defs args i w lv' body
          acc ← chk b (if op == "prod" then acc * v else if op == "max" then max acc v
            else if op == "lcm" then Nat.lcm acc v else acc + v)
      k := k + 1
    return acc
  | .iter id acc lo hi incl filt init body => do
    let l ← evalE b defs args i w lv lo
    let h ← evalE b defs args i w lv hi
    let stop := if incl then h + 1 else h
    let mut a ← evalE b defs args i w lv init
    let mut k := l
    while k < stop do
      tick b
      let lv' := (lv.insert id k).insert acc a
      if (← evalE b defs args i w lv' filt) != 0 then
        a ← evalE b defs args i w lv' body
      k := k + 1
    return a
  | .call f xs => do
    tick b
    let mut vs : Array Nat := #[]
    for x in xs do vs := vs.push (← evalE b defs args i w lv x)
    let some d := defs.get? f | throw "unknown callee"
    evalDef b defs d vs

/-- ℤ-valued subterms (see `trI`). -/
partial def evalI (b : Budget) (defs : Std.HashMap Name FnDef) (args : Array Nat) (i : Nat)
    (w : Array Nat) (lv : Std.HashMap Nat Nat) : E → IRM Int
  | .prim "ofnat" [x] => do pure (Int.ofNat (← evalE b defs args i w lv x))
  | .prim "ineg" [x] => do pure (- (← evalI b defs args i w lv x))
  | .prim "isign" [x] => do pure (← evalI b defs args i w lv x).sign
  | .prim "qnum" [x] => do pure (← evalQ b defs args i w lv x).1
  | .bin op x y => do
    let a ← evalI b defs args i w lv x
    match op with
    | "iadd" => chkI b (a + (← evalI b defs args i w lv y))
    | "isub" => chkI b (a - (← evalI b defs args i w lv y))
    | "imul" => chkI b (a * (← evalI b defs args i w lv y))
    | "ipow" =>
      let c ← evalE b defs args i w lv y
      -- Int.pow is Nat.pow on natAbs: Lean's runtime panics for exponent > 2^32-1 (see "pow")
      if c > 4294967295 then throw "runtime limit: Nat.pow exponent > 2^32-1"
      else if c == 0 then pure 1
      else if a.natAbs ≤ 1 then pure (if a == -1 && c % 2 == 1 then -1 else if a == -1 then 1 else a)
      else if c * (a.natAbs.log2 + 1) > b.maxBits + 64 then throw "size budget"
      else chkI b (a ^ c)
    | _ => throw "ill-typed ℤ node"
  | .ite c t e => do
    if (← evalE b defs args i w lv c) != 0 then evalI b defs args i w lv t else evalI b defs args i w lv e
  | .fold op id lo hi incl filt body => do
    let l ← evalE b defs args i w lv lo
    let h ← evalE b defs args i w lv hi
    let stop := if incl then h + 1 else h
    let mut acc : Int := if op == "iprod" then 1 else 0
    let mut k := l
    while k < stop do
      tick b
      let lv' := lv.insert id k
      if (← evalE b defs args i w lv' filt) != 0 then
        let v ← evalI b defs args i w lv' body
        acc ← chkI b (if op == "iprod" then acc * v else acc + v)
      k := k + 1
    return acc
  | _ => throw "ill-typed ℤ node"

/-- ℚ-valued subterms (see `trQ`), as normalized `(num, den)`. -/
partial def evalQ (b : Budget) (defs : Std.HashMap Name FnDef) (args : Array Nat) (i : Nat)
    (w : Array Nat) (lv : Std.HashMap Nat Nat) : E → IRM (Int × Nat)
  | .prim "qofnat" [x] => do pure (Int.ofNat (← evalE b defs args i w lv x), 1)
  | .prim "qofint" [x] => do pure ((← evalI b defs args i w lv x), 1)
  | .prim "qneg" [x] => do
    let (n, d) ← evalQ b defs args i w lv x
    pure (-n, d)
  | .prim "qinv" [x] => do
    let (n, d) ← evalQ b defs args i w lv x
    if n == 0 then pure (0, 1)
    else pure (if n < 0 then -(Int.ofNat d) else Int.ofNat d, n.natAbs)
  | .bin op x y => do
    let (an, ad) ← evalQ b defs args i w lv x
    if op == "qpow" then
      let c ← evalE b defs args i w lv y
      -- Lean evaluates the power on numerator and denominator; keep the exponent within the budget
      if c > b.maxBits + 64 then throw "size budget"
      if c * (an.natAbs.log2 + ad.log2 + 2) > 2 * b.maxBits + 128 then throw "size budget"
      return (← chkI b (an ^ c), ← chk b (ad ^ c))
    let (bn, bd) ← evalQ b defs args i w lv y
    match op with
    | "qadd" => qnorm b (an * Int.ofNat bd + bn * Int.ofNat ad) (ad * bd)
    | "qsub" => qnorm b (an * Int.ofNat bd - bn * Int.ofNat ad) (ad * bd)
    | "qmul" => qnorm b (an * bn) (ad * bd)
    | "qdiv" =>
      if bn == 0 then pure (0, 1)
      else qnorm b (an * (if bn < 0 then -(Int.ofNat bd) else Int.ofNat bd)) (ad * bn.natAbs)
    | _ => throw "ill-typed ℚ node"
  | .ite c t e => do
    if (← evalE b defs args i w lv c) != 0 then evalQ b defs args i w lv t else evalQ b defs args i w lv e
  | .fold op id lo hi incl filt body => do
    let l ← evalE b defs args i w lv lo
    let h ← evalE b defs args i w lv hi
    let stop := if incl then h + 1 else h
    let mut acc : Int × Nat := if op == "qprod" then (1, 1) else (0, 1)
    let mut k := l
    while k < stop do
      tick b
      let lv' := lv.insert id k
      if (← evalE b defs args i w lv' filt) != 0 then
        let (vn, vd) ← evalQ b defs args i w lv' body
        acc ← if op == "qprod" then qnorm b (acc.1 * vn) (acc.2 * vd)
          else qnorm b (acc.1 * Int.ofNat vd + vn * Int.ofNat acc.2) (acc.2 * vd)
      k := k + 1
    return acc
  | _ => throw "ill-typed ℚ node"

partial def evalDef (b : Budget) (defs : Std.HashMap Name FnDef) (d : FnDef) (vs : Array Nat) : IRM Nat := do
  match d with
  | .direct _ e => evalE b defs vs 0 #[] {} e
  | .recur _ j bases step =>
    let K := bases.length
    let n := vs.getD j 0
    -- the reference is Lean's compiled definition, which evaluates this recursion naively
    -- (exponential for K ≥ 2): refuse inputs whose naive call tree exceeds the budget
    if K ≥ 2 && naiveCost K step.prevs n b.naiveCalls > b.naiveCalls then throw "naive-recursion budget"
    let mut w : Array Nat := #[]
    for e in bases do w := w.push (← evalE b defs vs 0 #[] {} e)
    if n < K then return w[n]!
    for m in [0:n - K + 1] do
      tick b
      let nv ← evalE b defs vs m w {} step
      w := (w.extract 1 K).push nv
    return w[K - 1]!
end

def runIR (defs : Std.HashMap Name FnDef) (n : Name) (xs : List Nat) : Option Nat :=
  match defs.get? n with
  | none => none
  | some d => match (evalDef {} defs d xs.toArray).run 0 with
    | .ok (v, _) => some v
    | .error _ => none

def u64Max : Nat := 2 ^ 64 - 1

unsafe def evalN (env : Environment) (n : Name) (arity : Nat) (args : List Nat) : Except String Nat := do
  match arity, args with
  | 1, [a] => return (← env.evalConst (Nat → Nat) {} n (checkMeta := false)) a
  | 2, [a, b] => return (← env.evalConst (Nat → Nat → Nat) {} n (checkMeta := false)) a b
  | 3, [a, b, c] => return (← env.evalConst (Nat → Nat → Nat → Nat) {} n (checkMeta := false)) a b c
  | _, _ => throw "arity"

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Test inputs. "Heavy" functions (recursion, loops, pow, heavy builtins — directly or through
calls) get arguments ≤ 200; others also get 2^32-1, 2^63, 2^64-1. The interpreter budget then
decides which inputs are actually evaluated. -/
def inputs (arity : Nat) (bounded : Bool) (seed : UInt64) : Array (List Nat) := Id.run do
  let small : List Nat := [0, 1, 2, 3, 5, 7, 10, 16, 31, 64]
  let big : List Nat := if bounded then [100, 199] else [2 ^ 32 - 1, 2 ^ 63, 2 ^ 64 - 1]
  let vals := small ++ big
  let mut out : Array (List Nat) := #[]
  match arity with
  | 1 => for a in vals do out := out.push [a]
  | 2 => for a in vals do for b in vals do out := out.push [a, b]
  | _ =>
    let sm := if bounded then small.take 4 else small.take 6
    for a in sm ++ big do for b in sm ++ big do for c in sm ++ big do out := out.push [a, b, c]
  let mut s := seed
  -- fewer random inputs for heavy functions: each one may run long loops in interpreted code
  for _ in List.range (if bounded then 60 else 300) do
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
  -- Progress goes to a FILE: output of IO.println inside #eval is captured by Lean and only
  -- emitted when the command finishes, so it cannot show where a slow or killed run is.
  let prog ← IO.FS.Handle.mk (out "progress.log") .write
  let t0 ← IO.monoMsNow
  let progress (msg : String) : IO Unit := do
    prog.putStrLn s!"{((← IO.monoMsNow) - t0) / 1000}s {msg}"; prog.flush
  let wanted := (← IO.FS.lines modsPath).filter (· ≠ "") |>.map fun l =>
    ((l.splitOn "\t").drop 1).foldl Name.mkStr .anonymous
  -- 1. candidates
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
  progress s!"candidates={cands.size}; extracting"
  -- 2. extract
  let mut defs : Std.HashMap Name FnDef := {}
  let mut blocked : Array (Name × String) := #[]
  for (n, k) in cands do
    progress s!"extract {n}"
    match ← (try extract n k catch e => do pure (.error s!"exception: {← e.toMessageData.toString}")) with
    | .ok d => defs := defs.insert n d
    | .error r => blocked := blocked.push (n, r)
  progress s!"extraction done: translated={defs.size} blocked={blocked.size}"
  -- 3. closure over calls
  let mut changed := true
  while changed do
    changed := false
    for (n, d) in defs.toList do
      if let some bad := d.calls.find? (fun c => !defs.contains c) then
        defs := defs.erase n
        blocked := blocked.push (n, s!"calls untranslated function {bad}")
        changed := true
  -- 4. dependency order
  let names := (defs.toList.map (·.1)).toArray.qsort (fun a b => a.toString < b.toString)
  let mut order : Array Name := #[]
  let mut placed : Std.HashSet Name := {}
  while order.size < names.size do
    let before := order.size
    for n in names do
      if !placed.contains n && (defs.get! n).calls.all placed.contains then
        order := order.push n; placed := placed.insert n
    if order.size == before then throwError "call cycle among translated functions"
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
  let hdr := "/* Generated by lean-m2/tools/mathir_body.lean (MathIR v2). Do not edit. */\n#ifndef LM2_GEN_H\n#define LM2_GEN_H\n#include <stdint.h>\n#define LM2_OK 0\n#define LM2_OVERFLOW 1\n#define LM2_ERR_NULL (-1)\n" ++
    String.join (order.toList.map fun n => s!"int32_t {cSym n}({cParams (defs.get! n).arity});\n#define LM2_FN_{symOf.get! n} {idxOf.get! n}u\n") ++
    "int32_t lm2_gen_call(uint32_t fn, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t *out);\nuint32_t lm2_gen_count(void);\n#endif\n"
  let cBody := "/* Generated by lean-m2/tools/mathir_body.lean (MathIR v2). Do not edit.\n   Compiled only by CompCert. Every operation is checked (lm2_nat.h). */\n#include \"lm2_nat.h\"\n#include \"lm2_wide.h\"\n#include \"lm2_gen.h\"\n\n" ++
    String.join (order.toList.map fun n =>
      cFunctionW cSym n (defs.get! n) ++ "\n" ++ cFunction cSym n (defs.get! n) ++ "\n" ++ cWrapper cSym n (defs.get! n) ++ "\n") ++
    "int32_t lm2_gen_call(uint32_t fn, uint64_t a0, uint64_t a1, uint64_t a2, uint64_t *out) {\n  (void)a0; (void)a1; (void)a2;\n  switch (fn) {\n" ++
    String.join (order.toList.mapIdx fun i n =>
      let as := (List.range (defs.get! n).arity).map (s!"a{·}")
      s!"  case {i}u: return {cSym n}({", ".intercalate (as ++ ["out"])});\n") ++
    "  default: return LM2_ERR_NULL;\n  }\n}\n" ++ s!"uint32_t lm2_gen_count(void) \{ return {order.size}u; }\n"
  IO.FS.writeFile (out "lm2_gen.h") hdr
  IO.FS.writeFile (out "lm2_gen.c") cBody
  -- 6. Modula-2
  let mDef := "DEFINITION MODULE LM2Gen;\n(* Generated by lean-m2/tools/mathir_body.lean (MathIR v2). Do not edit.\n   Native Modula-2: NOT a wrapper around the C code. *)\nCONST\n  Ok = 0;\n  Overflow = 1;\n" ++
    String.join (order.toList.mapIdx fun i n => s!"  Fn{symOf.get! n} = {i};\n") ++
    String.join (order.toList.map fun n => s!"PROCEDURE {mSym n} ({mParams (defs.get! n).arity}) : INTEGER;\n") ++
    "PROCEDURE Call (fn: CARDINAL; a0, a1, a2: LONGCARD; VAR out: LONGCARD) : INTEGER;\nEND LM2Gen.\n"
  let mMod := "IMPLEMENTATION MODULE LM2Gen;\n(* Generated by lean-m2/tools/mathir_body.lean (MathIR v2). Do not edit. *)\nIMPORT LM2Nat, LM2Wide;\n\n" ++
    String.join (order.toList.map fun n =>
      mProcedureW mSym n (defs.get! n) ++ "\n" ++ mProcedure mSym n (defs.get! n) ++ "\n" ++ mWrapper mSym n (defs.get! n) ++ "\n") ++
    "PROCEDURE Call (fn: CARDINAL; a0, a1, a2: LONGCARD; VAR out: LONGCARD) : INTEGER;\nBEGIN\n  CASE fn OF\n" ++
    String.join (order.toList.mapIdx fun i n =>
      let as := (List.range (defs.get! n).arity).map (s!"a{·}")
      s!"  | {i}: RETURN {mSym n}({", ".intercalate (as ++ ["out"])})\n") ++
    "  ELSE RETURN -1\n  END\nEND Call;\n\nEND LM2Gen.\n"
  IO.FS.writeFile (out "LM2Gen.def") mDef
  IO.FS.writeFile (out "LM2Gen.mod") mMod
  IO.FS.writeFile (out "lm2_gen_bind.def")
    "DEFINITION MODULE FOR \"C\" lm2_gen_bind;\n(* Generated. Binding to the CompCert-compiled dispatcher in lm2_gen.c. *)\nFROM SYSTEM IMPORT ADDRESS;\nEXPORT UNQUALIFIED lm2_gen_call, lm2_gen_count;\nPROCEDURE lm2_gen_call (fn: CARDINAL; a0, a1, a2: LONGCARD; out: ADDRESS) : INTEGER;\nPROCEDURE lm2_gen_count () : CARDINAL;\nEND lm2_gen_bind.\n"
  -- 7. reference vectors
  let mut bounded : Std.HashMap Name Bool := {}
  for n in order do
    bounded := bounded.insert n ((defs.get! n).heavy || (defs.get! n).calls.any (bounded.getD · false))
  let mut cFn := ""; let mut cA0 := ""; let mut cA1 := ""; let mut cA2 := ""; let mut cSt := ""; let mut cV := ""
  let mut ncases := 0; let mut nok := 0; let mut skipped := 0
  let mut evalFail : Array (Name × String) := #[]
  let mut mismatch : Array (Name × List Nat × Nat × Nat) := #[]
  for h : i in [0:order.size] do
    let n := order[i]
    let d := defs.get! n
    progress s!"eval {i + 1}/{order.size} {n} (bounded={bounded.getD n false})"
    for xs in inputs d.arity (bounded.getD n false) (0x5EED0000 + i.toUInt64) do
      let irv? := runIR defs n xs
      if irv?.isNone then
        skipped := skipped + 1
        continue
      let irv := irv?.getD 0
      -- logged before the call: a runtime panic in compiled corpus code kills the process
      -- without flushing `#eval` output, so this line is the only record of the failing input
      progress s!"  lean {n} {xs}"
      match unsafe evalN env n d.arity xs with
      | .error e => evalFail := evalFail.push (n, e); break
      | .ok v =>
        if v != irv then mismatch := mismatch.push (n, xs, v, irv)
        let (st, val) := if v ≤ u64Max then (0, v) else (1, 0)
        let pad := xs ++ List.replicate (3 - xs.length) 0
        cFn := cFn ++ s!"{i}u,"; cA0 := cA0 ++ s!"{pad[0]!}ULL,"; cA1 := cA1 ++ s!"{pad[1]!}ULL,"
        cA2 := cA2 ++ s!"{pad[2]!}ULL,"; cSt := cSt ++ s!"{st},"; cV := cV ++ s!"{val}ULL,"
        ncases := ncases + 1
        if st == 0 then nok := nok + 1
  unless evalFail.isEmpty do throwError m!"reference evaluation failed: {evalFail.toList.map (·.1)}"
  unless mismatch.isEmpty do
    let first := mismatch.toList.take 10 |>.map fun (n, xs, v, w) => s!"{n} {xs}: lean={v} ir={w}"
    throwError m!"EXTRACTION FIDELITY FAILURE ({mismatch.size} mismatches): {first}"
  progress s!"reference vectors done: cases={ncases} skipped={skipped}"
  IO.FS.writeFile (out "lm2_gen_cases.c") <|
    "/* Generated by mathir_body.lean: Lean-evaluated reference values. Do not edit. */\n#include <stdint.h>\n#include <stddef.h>\n" ++
    s!"#define N {ncases}u\nstatic const uint32_t F[N]=\{{cFn}};\nstatic const uint64_t A0[N]=\{{cA0}};\nstatic const uint64_t A1[N]=\{{cA1}};\nstatic const uint64_t A2[N]=\{{cA2}};\nstatic const int32_t ST[N]=\{{cSt}};\nstatic const uint64_t V[N]=\{{cV}};\n" ++
    "uint32_t lm2_gen_case_count(void) { return N; }\nint32_t lm2_gen_case_get(uint32_t i, uint32_t *f, uint64_t *a0, uint64_t *a1, uint64_t *a2, int32_t *st, uint64_t *v) {\n  if (i >= N || !f || !a0 || !a1 || !a2 || !st || !v) return -1;\n  *f = F[i]; *a0 = A0[i]; *a1 = A1[i]; *a2 = A2[i]; *st = ST[i]; *v = V[i];\n  return 0;\n}\n"
  -- 8. MathIR + reports
  let irJson := Json.mkObj [
    ("schema", toJson "mathir/2"), ("fragment", toJson "NatLoops v2"),
    ("lean", toJson Lean.versionString),
    ("functions", toJson (order.toList.mapIdx fun i n =>
      let d := defs.get! n
      Json.mkObj ([("id", toJson i), ("name", toJson n.toString), ("c_symbol", toJson (cSym n)),
        ("m2_symbol", toJson (mSym n)), ("arity", toJson d.arity)] ++
        match d with
        | .direct _ e => [("kind", toJson "direct"), ("body", e.json)]
        | .recur _ j bs s => [("kind", toJson "rec"), ("rec_arg", toJson j), ("lookback", toJson bs.length),
            ("bases", toJson (bs.map E.json)), ("step", s.json)])))]
  IO.FS.writeFile (out "mathir.json") (irJson.pretty ++ "\n")
  let blockedSorted := blocked.qsort (fun a b => a.1.toString < b.1.toString)
  IO.FS.writeFile (out "blocked.json") ((toJson (blockedSorted.map fun (n, r) =>
    Json.mkObj [("name", toJson n.toString), ("reason", toJson r)])).pretty ++ "\n")
  let mut hist : Std.HashMap String Nat := {}
  for (_, r) in blocked do
    let key := if r.startsWith "unsupported: " then "unsupported constant"
      else if r.startsWith "unsupported predicate: " then "unsupported predicate"
      else if r.startsWith "unsupported Finset source: " then "unsupported Finset source"
      else if r.startsWith "calls untranslated" then "calls untranslated function" else r
    hist := hist.insert key (hist.getD key 0 + 1)
  let histLines := (hist.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.map fun (k, v) => s!"  {v}  {k}"
  let mut consts : Std.HashMap String Nat := {}
  for (_, r) in blocked do
    for pfx in ["unsupported: ", "unsupported predicate: ", "unsupported Finset source: "] do
      if r.startsWith pfx then
        let k := (r.drop pfx.length).toString
        consts := consts.insert k (consts.getD k 0 + 1)
  let topConsts := ((consts.toList.toArray.qsort (fun a b => a.2 > b.2)).toList.take 20).map fun (k, v) => s!"  {v}  {k}"
  let kindOf (n : Name) : String := match defs.get! n with
    | .direct .. => "" | .recur _ _ bs _ => s!", rec K={bs.length}"
  let summary := s!"MATHIR candidates={cands.size} translated={order.size} blocked={blocked.size} cases={ncases} ok={nok} overflow={ncases - nok} skipped_over_budget={skipped} ir_fidelity_mismatches=0"
  let report := summary ++ "\ntranslated:\n" ++
    String.join (order.toList.map fun n => s!"  {n} ({(defs.get! n).arity}-ary{kindOf n})\n") ++
    "blocked reasons:\n" ++ "\n".intercalate histLines ++ "\ntop unsupported constants / predicates / sources:\n" ++ "\n".intercalate topConsts ++ "\n"
  IO.FS.writeFile (out "report.txt") report
  -- per-function blocking reasons (sorted by name): the work list for widening the fragment
  IO.FS.writeFile (out "blocked.txt") <| String.join <|
    ((blocked.qsort (fun x y => x.1.toString < y.1.toString)).toList.map fun (n, r) => s!"{n}\t{r}\n")
  IO.println summary
