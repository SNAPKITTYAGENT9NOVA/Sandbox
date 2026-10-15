/-
LEAN-M2-CC-001 · G1 inventory, implemented in Lean (inventory schema 2.0.0).

Run inside the pinned toolchain (no project build needed):
    lean --run lean-m2/tools/G1Inventory.lean <lean-project-root> <out-dir>
    lean --run lean-m2/tools/G1Inventory.lean --selftest

What is canonical here (no re-implementation of Lean or Lake syntax):
  * headers are parsed by Lean's own `Lean.Parser.parseHeader`, and imports are read with
    `Lean.Elab.HeaderSyntax.imports` — exactly what the elaborator uses;
  * module names are `Lean.Name` values built from path components and rendered with
    `Name.toString` (so `Arxiv/0805.3777/X.lean` is `Arxiv.«0805.3777».X`);
  * `lakefile.toml` is read with Lake's own TOML loader `Lake.Toml.loadToml`.

Self-contained part: SHA-256 (FIPS 180-4). `--selftest` checks it against the standard test
vectors; CI additionally compares every file hash with `sha256sum`.

Outputs (deterministic: sorted inputs, `Json.pretty` with sorted keys, no timestamps):
  inventory.json, imports.json, source-hashes.json, source-tree.sha256
Exit code 1 (fail closed) on any header parse error, missing internal import, module-name
collision, or import cycle.
-/
import Lean
import Lake.Toml

open Lean

namespace LeanM2.Sha256

def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Message padding: 0x80, zeros to 56 mod 64, then the 64-bit big-endian bit length. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut bs := msg.push 0x80
  while bs.size % 64 != 56 do
    bs := bs.push 0
  for i in [0:8] do
    bs := bs.push ((bitLen >>> (8 * (7 - i)).toUInt64).toUInt8)
  return bs

def compress (h : Array UInt32) (bs : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    let i := off + 4 * t
    w := w.push ((bs.get! i).toUInt32 <<< 24 ||| (bs.get! (i + 1)).toUInt32 <<< 16 |||
                 (bs.get! (i + 2)).toUInt32 <<< 8 ||| (bs.get! (i + 3)).toUInt32)
  for t in [16:64] do
    let x := w[t - 15]!
    let y := w[t - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let bigS1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + bigS1 + ch + K[t]! + w[t]!
    let bigS0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bigS0 + maj
    hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hex8 (x : UInt32) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut s := ""
  for i in [0:8] do
    let nib := ((x >>> (4 * (7 - i)).toUInt32) &&& 0xf).toNat
    s := s.push digits[nib]!
  return s

def digestHex (msg : ByteArray) : String := Id.run do
  let bs := pad msg
  let mut h := H0
  let mut off := 0
  while off < bs.size do
    h := compress h bs off
    off := off + 64
  return h.foldl (fun s x => s ++ hex8 x) ""

end LeanM2.Sha256

namespace LeanM2.G1

open LeanM2.Sha256 (digestHex)

def corpusDirs : List String :=
  ["FormalConjectures", "FormalConjecturesForMathlib", "FormalConjecturesUtil", "FormalConjecturesTest"]

/-- Recursively list `.lean` files as relative path component lists, skipping VCS/build dirs. -/
partial def walk (root : System.FilePath) (rel : List String) : IO (Array (List String)) := do
  let mut out := #[]
  let dir := rel.foldl (· / ·) root
  for entry in ← dir.readDir do
    let name := entry.fileName
    if ← entry.path.isDir then
      unless name == ".git" || name == ".lake" || name == "lake-packages" do
        out := out ++ (← walk root (rel ++ [name]))
    else if entry.path.extension == some "lean" then
      out := out.push (rel ++ [name])
  return out

def relString (comps : List String) : String := "/".intercalate comps

/-- Module components of a relative path: strip the `.lean` extension from the last component. -/
def moduleComps (comps : List String) : List String :=
  match comps.reverse with
  | [] => []
  | last :: revInit => (revInit.reverse) ++ [(System.FilePath.mk last).withExtension "" |>.toString]

def mkName (comps : List String) : Name := comps.foldl Name.mkStr .anonymous

/-- Lake glob semantics on components: `A` = A; `A.*` = A and submodules; `A.+` = strict submodules. -/
def globMatch (glob : String) (comps : List String) : Bool :=
  let parts := glob.splitOn "."
  match parts.getLast? with
  | some "*" => let b := parts.dropLast; comps.take b.length == b
  | some "+" => let b := parts.dropLast; comps.length > b.length && comps.take b.length == b
  | _ => comps == parts

structure LakeCfg where
  libs : Array (String × Array String)        -- lean_lib name, globs
  exes : Array (String × String × String)     -- lean_exe name, srcDir, root
  defaultTargets : Array String
  testDriver : Option String

def tomlStr? : Lake.Toml.Value → Option String
  | .string _ s => some s
  | _ => none

def tomlStrs (v? : Option Lake.Toml.Value) : Array String :=
  match v? with
  | some (.array _ xs) => xs.filterMap tomlStr?
  | _ => #[]

def tomlTables (v? : Option Lake.Toml.Value) : Array Lake.Toml.Table :=
  match v? with
  | some (.array _ xs) => xs.filterMap fun | .table _ t => some t | _ => none
  | _ => #[]

def loadLake (root : System.FilePath) : IO LakeCfg := do
  let path := root / "lakefile.toml"
  let src ← IO.FS.readFile path
  let ictx := Parser.mkInputContext src path.toString
  let t ← match (← (Lake.Toml.loadToml ictx).toBaseIO) with
    | .ok t => pure t
    | .error msgs =>
      let ms ← msgs.toList.mapM (·.toString)
      throw <| IO.userError s!"lakefile.toml: {"; ".intercalate ms}"
  let libs := (tomlTables (t.find? `lean_lib)).filterMap fun lt => do
    let name ← (lt.find? `name).bind tomlStr?
    let globs := tomlStrs (lt.find? `globs)
    pure (name, if globs.isEmpty then #[name] else globs)
  let exes := (tomlTables (t.find? `lean_exe)).filterMap fun et => do
    let name ← (et.find? `name).bind tomlStr?
    let srcDir := ((et.find? `srcDir).bind tomlStr?).getD "."
    let root := ((et.find? `root).bind tomlStr?).getD name
    pure (name, srcDir, root)
  return { libs, exes,
           defaultTargets := tomlStrs (t.find? `defaultTargets),
           testDriver := (t.find? `testDriver).bind tomlStr? }

structure ImportRec where
  comps : List String
  importAll : Bool
  isExported : Bool
  isMeta : Bool

structure FileRec where
  rel : String
  sha : String
  bytes : Nat
  dclass : String
  modComps : Option (List String)   -- none for lake_exe roots
  exe : Option String
  isModule : Bool
  isPrelude : Bool
  parseError : Option String
  imports : Array ImportRec

def nameComps (n : Name) : List String :=
  n.components.map fun
    | .str _ s => s
    | c => c.toString

def parseHeaderOf (src fileName : String) : IO (Except String (Bool × Bool × Array Import)) := do
  let inputCtx := Parser.mkInputContext src fileName
  let (header, _, messages) ← Parser.parseHeader inputCtx
  if messages.hasErrors then
    let ms ← messages.toList.mapM (·.toString)
    return .error ("; ".intercalate ms)
  let isModule := Lean.Elab.HeaderSyntax.isModule header
  let isPrelude := !header.raw[1].isNone
  return .ok (isModule, isPrelude, Lean.Elab.HeaderSyntax.imports header (includeInit := false))

def strLt (a b : String) : Bool := a < b

def run (root out : System.FilePath) : IO UInt32 := do
  let cfg ← loadLake root
  let exeFiles : Array (String × String) := cfg.exes.map fun (n, src, r) =>
    let base := if src == "." then [] else src.splitOn "/"
    (relString (base ++ (r.splitOn ".").dropLast ++ [(r.splitOn ".").getLast! ++ ".lean"]), n)
  let paths := (← walk root []).qsort (fun a b => strLt (relString a) (relString b))
  let mut files : Array FileRec := #[]
  let mut errors : Array (String × String) := #[]
  for comps in paths do
    let rel := relString comps
    let raw ← IO.FS.readBinFile (comps.foldl (· / ·) root)
    let text := String.fromUTF8! raw
    let top := comps.head!
    let dclass := if corpusDirs.contains top then top else if comps.length == 1 then "root" else "other"
    let exe := (exeFiles.find? (·.1 == rel)).map (·.2)
    let (isMod, isPre, imps, perr) ← match ← parseHeaderOf text rel with
      | .ok (m, p, is) => pure (m, p, is, none)
      | .error e => do pure (false, false, #[], some e)
    if let some e := perr then errors := errors.push (rel, e)
    files := files.push {
      rel, sha := digestHex raw, bytes := raw.size, dclass, exe, isModule := isMod, isPrelude := isPre,
      parseError := perr,
      modComps := if exe.isSome then none else some (moduleComps comps),
      imports := imps.map fun i =>
        { comps := nameComps i.module, importAll := i.importAll, isExported := i.isExported,
          isMeta := i.isMeta } }

  -- module table (rendered names are injective on component lists)
  let mut modOf : Std.HashMap String Nat := {}
  for h : idx in [0:files.size] do
    if let some mc := files[idx].modComps then
      let key := (mkName mc).toString
      if modOf.contains key then errors := errors.push (files[idx].rel, s!"module name collision: {key}")
      modOf := modOf.insert key idx
  let internalRoots : List String :=
    (cfg.libs.map (·.1)).toList ++ (files.filterMap (·.modComps)).toList.filterMap (·.head?)

  -- resolution + graph
  let mut graph : Array (Array String) := Array.replicate files.size #[]
  let mut missing : Array (String × String) := #[]
  let mut externalRoots : Std.HashMap String Nat := {}
  let mut resolution : Array (Array String) := Array.replicate files.size #[]
  for h : idx in [0:files.size] do
    let mut deps : Array String := #[]
    let mut res : Array String := #[]
    for imp in files[idx].imports do
      let key := (mkName imp.comps).toString
      if modOf.contains key then
        res := res.push "internal"
        unless deps.contains key do deps := deps.push key
      else if internalRoots.contains imp.comps.head! then
        res := res.push "missing-internal"
        missing := missing.push (files[idx].rel, key)
      else
        res := res.push "external-unresolved"
        externalRoots := externalRoots.insert imp.comps.head! (externalRoots.getD imp.comps.head! 0 + 1)
    graph := graph.set! idx (deps.qsort strLt)
    resolution := resolution.set! idx res

  -- Lake target closure
  let closure (seeds : Array String) : Std.HashSet String := Id.run do
    let mut seen : Std.HashSet String := {}
    let mut stack := seeds
    while !stack.isEmpty do
      let m := stack.back!
      stack := stack.pop
      if seen.contains m then continue
      match modOf.get? m with
      | none => pure ()
      | some i =>
        seen := seen.insert m
        stack := stack ++ graph[i]!
    return seen
  let mut targetsOf : Std.HashMap String (Array String) := {}
  for (lib, globs) in cfg.libs do
    let seeds := files.filterMap fun f => f.modComps.bind fun mc =>
      if globs.any (globMatch · mc) then some (mkName mc).toString else none
    for m in closure seeds do
      targetsOf := targetsOf.insert m ((targetsOf.getD m #[]).push lib)
  for h : idx in [0:files.size] do
    if let some e := files[idx].exe then
      for m in closure graph[idx]! do
        targetsOf := targetsOf.insert m ((targetsOf.getD m #[]).push s!"exe:{e}")

  -- topological order (Kahn; smallest rendered name first => deterministic)
  let mods := (modOf.toList.map (·.1)).toArray.qsort strLt
  let mut indeg : Std.HashMap String Nat := {}
  let mut rdeps : Std.HashMap String (Array String) := {}
  for m in mods do
    indeg := indeg.insert m (graph[modOf.get! m]!).size
    for d in graph[modOf.get! m]! do
      rdeps := rdeps.insert d ((rdeps.getD d #[]).push m)
  let mut ready := mods.filter (indeg.get! · == 0)
  let mut order : Array String := #[]
  while !ready.isEmpty do
    let m := ready.foldl (fun acc x => if strLt x acc then x else acc) ready[0]!
    ready := ready.erase m
    order := order.push m
    for r in rdeps.getD m #[] do
      let k := indeg.get! r - 1
      indeg := indeg.insert r k
      if k == 0 then ready := ready.push r
  let cycle := (mods.filter (indeg.get! · > 0))

  -- outputs
  let treeLines := files.foldl (fun s f => s ++ s!"{f.sha}  {f.rel}\n") ""
  let treeSha := digestHex treeLines.toUTF8
  let fileJson (idx : Nat) (f : FileRec) : Json :=
    let tg := match f.modComps with
      | some mc => ((targetsOf.getD (mkName mc).toString #[]).qsort strLt)
      | none => #[s!"exe:{f.exe.getD ""}"]
    Json.mkObj [
      ("path", toJson f.rel), ("sha256", toJson f.sha), ("bytes", toJson f.bytes),
      ("directory_class", toJson f.dclass),
      ("module_name", toJson (f.modComps.map fun mc => (mkName mc).toString)),
      ("module_components", toJson f.modComps),
      ("lake_exe", toJson f.exe),
      ("lean_module_system", toJson f.isModule), ("prelude", toJson f.isPrelude),
      ("header_parse_error", toJson f.parseError),
      ("imports", toJson ((f.imports.zip (resolution[idx]!)).map fun (i, r) => Json.mkObj [
        ("module", toJson (mkName i.comps).toString), ("module_components", toJson i.comps),
        ("import_all", toJson i.importAll), ("is_exported", toJson i.isExported),
        ("is_meta", toJson i.isMeta), ("resolution", toJson r)])),
      ("lake_targets", toJson tg),
      ("built_by_default", toJson (tg.any cfg.defaultTargets.contains)),
      ("reachable", toJson !tg.isEmpty)]
  let filesJson := files.mapIdx fun idx f => fileJson idx f
  let countBy (key : FileRec → String) : Json :=
    Json.mkObj <| (files.foldl (fun (m : Std.HashMap String Nat) f => m.insert (key f) (m.getD (key f) 0 + 1)) {}).toList.map
      fun (k, v) => (k, toJson v)
  let builtByDefault := (filesJson.filter fun j => (j.getObjValAs? Bool "built_by_default").toOption == some true).size
  let unreachable := filesJson.filterMap fun j =>
    if (j.getObjValAs? Bool "reachable").toOption == some false then (j.getObjValAs? String "path").toOption else none
  let summary := Json.mkObj [
    ("contract", toJson "LEAN-M2-CC-001"), ("gate", toJson "G1"), ("inventory_schema", toJson "2.0.0"),
    ("tool", toJson "lean-m2/tools/G1Inventory.lean"), ("lean_version", toJson Lean.versionString),
    ("header_parser", toJson "Lean.Parser.parseHeader + Lean.Elab.HeaderSyntax.imports"),
    ("lakefile_parser", toJson "Lake.Toml.loadToml"),
    ("lean_files", toJson files.size), ("files_by_directory_class", countBy (·.dclass)),
    ("lean_module_system_files", toJson (files.filter (·.isModule)).size),
    ("non_module_files", toJson ((files.filter (!·.isModule)).map (·.rel))),
    ("header_parse_errors", toJson (errors.map fun (f, e) => Json.mkObj [("file", toJson f), ("error", toJson e)])),
    ("import_declarations", toJson (files.foldl (· + ·.imports.size) 0)),
    ("internal_import_edges", toJson (graph.foldl (· + ·.size) 0)),
    ("missing_internal_imports", toJson (missing.map fun (f, m) => Json.mkObj [("importer", toJson f), ("module", toJson m)])),
    ("external_import_roots", Json.mkObj (externalRoots.toList.map fun (k, v) => (k, toJson v))),
    ("lake_default_targets", toJson cfg.defaultTargets), ("lake_test_driver", toJson cfg.testDriver),
    ("lake_libs", Json.mkObj (cfg.libs.toList.map fun (n, g) => (n, toJson g))),
    ("files_built_by_default", toJson builtByDefault),
    ("unreachable_files", toJson unreachable),
    ("import_cycles", toJson cycle),
    ("source_tree_sha256", toJson treeSha),
    ("source_tree_sha256_definition", toJson "sha256 of sorted lines '<file sha256>  <relpath>\\n' over all .lean files outside .git/.lake")]
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "inventory.json") ((Json.mkObj [("summary", summary), ("files", toJson filesJson)]).pretty ++ "\n")
  IO.FS.writeFile (out / "imports.json") ((Json.mkObj [
    ("graph", Json.mkObj (mods.toList.map fun m => (m, toJson graph[modOf.get! m]!))),
    ("topological_order", toJson order), ("cycles", toJson cycle)]).pretty ++ "\n")
  IO.FS.writeFile (out / "source-hashes.json") ((Json.mkObj [
    ("source_tree_sha256", toJson treeSha),
    ("files", Json.mkObj (files.toList.map fun f => (f.rel, toJson f.sha)))]).pretty ++ "\n")
  IO.FS.writeFile (out / "source-tree.sha256") treeLines
  let blocked := !errors.isEmpty || !missing.isEmpty || !cycle.isEmpty
  IO.println s!"lean_files={files.size} imports={files.foldl (· + ·.imports.size) 0} internal_edges={graph.foldl (· + ·.size) 0} built_by_default={builtByDefault} parse_errors={errors.size} missing={missing.size} cycles={cycle.size} tree={treeSha}"
  IO.println s!"G1: {if blocked then "BLOCKED" else "PASS (pre-elaboration)"}"
  return if blocked then 1 else 0

/-- FIPS 180-4 / NIST test vectors. -/
def selftest : IO UInt32 := do
  let vectors : List (String × String) := [
    ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("The quick brown fox jumps over the lazy dog",
     "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592")]
  let mut ok := true
  for (msg, want) in vectors do
    let got := digestHex msg.toUTF8
    IO.println s!"{if got == want then "PASS" else "FAIL"} sha256({msg.length} chars) = {got}"
    if got != want then ok := false
  -- one million 'a' (NIST long-message vector)
  let million := ByteArray.mk (Array.replicate 1000000 (97 : UInt8))
  let got := digestHex million
  let want := "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  IO.println s!"{if got == want then "PASS" else "FAIL"} sha256(1e6 x 'a') = {got}"
  if got != want then ok := false
  return if ok then 0 else 1

end LeanM2.G1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--selftest"] => LeanM2.G1.selftest
  | [root, out] => LeanM2.G1.run root out
  | _ =>
    IO.eprintln "usage: G1Inventory.lean <lean-project-root> <out-dir> | --selftest"
    return 2
