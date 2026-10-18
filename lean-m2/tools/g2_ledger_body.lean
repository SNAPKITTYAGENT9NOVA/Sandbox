-- SPDX-License-Identifier: AGPL-3.0-only
-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
/-
LEAN-M2-CC-001 · G2 declaration and axiom ledger (body).

CI generates `Ledger.lean` = `import Lean` + one `import` per corpus module + this file,
and elaborates it with `lake env lean Ledger.lean` inside the pinned corpus checkout.
Using Lean's own frontend means imports and environment extensions load the canonical way.

Inputs (environment variables):
  LEDGER_MODS  TSV, one module per line: <rendered name> TAB <component> TAB <component> ...
               Components are passed explicitly because names like Arxiv.«0805.3777».X contain
               dots inside a component; a dotted string cannot be split back reliably.
  LEDGER_OUT   output path for JSON Lines (one object per constant)

Per constant, it records:
  * name, module, kind, safety, private, internal (auxiliary) flags;
  * noncomputable, extern, implemented_by — the trusted escape hatches relevant to extraction;
  * direct_sorry — whether its own type or value contains `sorry`;
  * axioms — the transitive set of axioms its type and value depend on, computed over
    kernel terms (memoized). This is the same quantity `#print axioms` reports, which
    includes `sorryAx` whenever a dependency uses `sorry`.

Ledger rows are emitted in moduleData order for each module, in the LEDGER_MODS order.
-/

open Lean

namespace LeanM2Ledger

def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def safetyOf : ConstantInfo → String
  | .defnInfo v =>
    match v.safety with
    | .safe => "safe"
    | .unsafe => "unsafe"
    | .partial => "partial"
  | ci => if ci.isUnsafe then "unsafe" else "safe"

/-- Transitive axiom dependencies of `root`, memoized across calls.
Iterative post-order traversal (no deep recursion). Kernel declarations are acyclic;
`onStack` only guards against that invariant being violated. -/
def axiomsOf (env : Environment) (memo : IO.Ref (Std.HashMap Name (Array Name)))
    (root : Name) : IO (Array Name) := do
  if let some r := (← memo.get)[root]? then return r
  let mut stack : Array (Name × Bool) := #[(root, false)]
  let mut onStack : NameSet := {}
  while !stack.isEmpty do
    let (n, expanded) := stack.back!
    stack := stack.pop
    if (← memo.get).contains n then continue
    match env.find? n with
    | none =>
      memo.modify (·.insert n #[])
    | some ci =>
      let deps := ci.getUsedConstantsAsSet.toList
      if expanded then
        let m ← memo.get
        let mut acc : NameSet := {}
        if ci matches .axiomInfo _ then acc := acc.insert n
        for d in deps do
          for a in m.getD d #[] do
            acc := acc.insert a
        let sorted := acc.toList.toArray.qsort (fun a b => a.toString < b.toString)
        memo.modify (·.insert n sorted)
        onStack := onStack.erase n
      else
        if onStack.contains n then continue
        onStack := onStack.insert n
        stack := stack.push (n, true)
        let m ← memo.get
        for d in deps do
          unless m.contains d || onStack.contains d do
            stack := stack.push (d, false)
  return (← memo.get).getD root #[]

/-- Type facts for G3 planning (only computed for candidate defs):
the constants mentioned in the type, whether the result sort is `Prop`, and the pretty type. -/
def typeInfo (ci : ConstantInfo) : MetaM (Array String × Bool × Bool × String) := do
  let consts := (ci.type.getUsedConstants.foldl (fun (s : NameSet) n => s.insert n) {}).toList
    |>.map Name.toString |>.toArray.qsort (· < ·)
  let retProp ← Meta.forallTelescopeReducing ci.type fun _ b => pure b.isProp
  -- result is a universe (`Type`, `Sort u`, ...): a type former, not a computation
  let retSort ← Meta.forallTelescopeReducing ci.type fun _ b => pure b.isSort
  let pp ← try pure (toString (← Meta.ppExpr ci.type)) catch _ => pure "<pp failed>"
  return (consts, retProp, retSort, pp)

end LeanM2Ledger

open LeanM2Ledger in
set_option maxHeartbeats 0 in
#eval show CoreM Unit from do
  let env ← getEnv
  let some modsPath ← IO.getEnv "LEDGER_MODS" | throwError "LEDGER_MODS is not set"
  let some outPath ← IO.getEnv "LEDGER_OUT" | throwError "LEDGER_OUT is not set"
  let wanted := (← IO.FS.lines modsPath).filter (· ≠ "") |>.map fun l =>
    let comps := (l.splitOn "\t").drop 1
    (comps.foldl Name.mkStr .anonymous, comps)
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let h ← IO.FS.Handle.mk outPath .write
  let mut rows := 0
  for (modName, modComps) in wanted do
    let some idx := env.header.moduleNames.findIdx? (· == modName)
      | throwError m!"LEDGER: module not in environment: {modName}"
    for ci in env.header.moduleData[idx]!.constants do
      let name := ci.name
      let axs ← axiomsOf env memo name
      let directSorry := ci.type.hasSorry || (ci.value? (allowOpaque := true) |>.any (·.hasSorry))
      let isCandidateShape := kindOf ci == "def" && safetyOf ci == "safe" &&
        !isNoncomputable env name && !name.isInternal
      let extra : List (String × Json) ← if isCandidateShape then do
          let (cs, rp, rs, pp) ← Meta.MetaM.run' (typeInfo ci)
          pure [("type_consts", toJson cs), ("returns_prop", toJson rp), ("returns_sort", toJson rs),
                ("type_pp", toJson pp)]
        else pure []
      let row := Json.mkObj <| extra ++ [
        ("name", toJson name.toString),
        ("module", toJson modName.toString),
        ("module_components", toJson modComps),
        ("kind", toJson (kindOf ci)),
        ("safety", toJson (safetyOf ci)),
        ("private", toJson (isPrivateName name)),
        ("internal", toJson name.isInternal),
        ("noncomputable", toJson (isNoncomputable env name)),
        ("extern", toJson (isExtern env name)),
        ("implemented_by", toJson ((Compiler.getImplementedBy? env name).map Name.toString)),
        ("direct_sorry", toJson directSorry),
        ("axioms", toJson (axs.map Name.toString))]
      h.putStrLn row.compress
      rows := rows + 1
  h.flush
  IO.println s!"LEDGER rows={rows} modules={wanted.size}"
