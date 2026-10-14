#!/usr/bin/env python3
"""LEAN-M2-CC-001 · G1 inventory (pre-elaboration).

Usage:
    python3 -I g1_inventory.py <lean-project-root> <out-dir>

What this establishes (from source text only, deterministically):
  * every .lean file outside .git/.lake, with SHA-256 and size;
  * the directory class of each file (the four corpus directories, plus 'other');
  * the Lean header of each file, read by a lexer that understands nested block
    comments, line comments, and the module system (`module`, `prelude`,
    `public`/`private`/`meta` import modifiers, `import all`);
  * the internal import graph, missing internal imports, and external import roots;
  * which files Lake's default targets build (lean_lib globs + import closure),
    which are tests or executables, and which no target reaches;
  * a topological order of internal modules (dependencies first).

What this does NOT establish (requires the Lean environment, gate G1b/G2):
  * that external imports (Mathlib, Lean, ...) resolve;
  * declarations, namespaces, kinds, axioms, `sorry` usage. The `lexical` block
    per file is a non-authoritative scan, flagged as such, for planning only.

Outputs are byte-deterministic for a given source tree (no timestamps inside).
"""
import hashlib, json, os, re, sys, tomllib

CORPUS_DIRS = ["FormalConjectures", "FormalConjecturesForMathlib",
               "FormalConjecturesUtil", "FormalConjecturesTest"]
SKIP_DIRS = {".git", ".lake", "lake-packages"}

# ---------------------------------------------------------------- lexer
IDENT_START = re.compile(r"[A-Za-z_À-\U0010FFFF«]")

PLAIN_COMPONENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*\Z")

def render_name(components):
    """Render a Lean Name the way Name.toString does for this corpus: a component that is not
    a plain identifier (digit-initial, or containing '.') is wrapped in «». Module names are
    component tuples; a dotted string without escaping is lossy ('Arxiv/0805.3777/X' is the
    three components Arxiv, «0805.3777», X — not four)."""
    return ".".join(c if PLAIN_COMPONENT.match(c) else f"«{c}»" for c in components)

class HeaderError(Exception):
    pass

def skip_ws_comments(s, i):
    n = len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j + 1
        elif s.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if s.startswith("/-", i):
                    depth += 1; i += 2
                elif s.startswith("-/", i):
                    depth -= 1; i += 2
                else:
                    i += 1
            if depth:
                raise HeaderError("unterminated block comment")
        else:
            break
    return i

def read_ident(s, i):
    """Read a possibly dotted, possibly «escaped» Lean identifier."""
    parts, n = [], len(s)
    while True:
        if i < n and s[i] == "«":
            j = s.find("»", i)
            if j < 0:
                raise HeaderError("unterminated «»")
            parts.append(s[i + 1:j]); i = j + 1
        else:
            m = re.compile(r"[^\s.«»()\[\]{},:;\"'`]+").match(s, i)
            if not m:
                raise HeaderError(f"expected identifier at offset {i}")
            parts.append(m.group(0)); i = m.end()
        if i < n and s[i] == "." and i + 1 < n and (s[i + 1] == "«" or IDENT_START.match(s[i + 1])):
            i += 1; continue
        return tuple(parts), i

def read_word(s, i):
    m = re.compile(r"[A-Za-z_]+").match(s, i)
    return (m.group(0), m.end()) if m else (None, i)

def parse_header(s):
    i = skip_ws_comments(s, 0)
    hdr = {"module": False, "prelude": False, "imports": []}
    w, j = read_word(s, i)
    if w == "module":
        hdr["module"] = True; i = skip_ws_comments(s, j); w, j = read_word(s, i)
    if w == "prelude":
        hdr["prelude"] = True; i = skip_ws_comments(s, j)
    while True:
        k, mods = i, []
        while True:
            w, j = read_word(s, k)
            if w in ("public", "private", "meta"):
                mods.append(w); k = skip_ws_comments(s, j)
            else:
                break
        if w != "import":
            # Not an import: the header ends at offset i, before any modifiers just read.
            # (e.g. `public section`, `meta def ...` are commands, not header syntax.)
            break
        k = skip_ws_comments(s, j)
        w2, j2 = read_word(s, k)
        imp_all = False
        if w2 == "all":
            # `import all X`: `all` followed by whitespace then an identifier
            imp_all = True; k = skip_ws_comments(s, j2)
        comps, k = read_ident(s, k)
        hdr["imports"].append({"module": render_name(comps), "module_components": list(comps),
                               "modifiers": mods, "all": imp_all})
        i = skip_ws_comments(s, k)
    hdr["header_end_offset"] = i
    return hdr

# ------------------------------------------------- non-authoritative lexical scan
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|public|meta)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example)\b",
    re.M)

def strip_comments(s):
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j
        elif s.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if s.startswith("/-", i): depth += 1; i += 2
                elif s.startswith("-/", i): depth -= 1; i += 2
                else:
                    if s[i] == "\n": out.append("\n")
                    i += 1
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            out.append('""'); i = j + 1
        else:
            out.append(s[i]); i += 1
    return "".join(out)

def lexical_scan(s):
    code = strip_comments(s)
    kinds = {}
    for m in DECL_RE.finditer(code):
        kinds[m.group(1)] = kinds.get(m.group(1), 0) + 1
    return {"authoritative": False,
            "decl_keyword_counts": dict(sorted(kinds.items())),
            "sorry_tokens": len(re.findall(r"(?<![\w.])sorry(?![\w])", code))}

# ---------------------------------------------------------------- lake targets
def glob_match(glob, comps):
    """Lake globs on module components: `A` = A; `A.*` = A and submodules; `A.+` = strict submodules."""
    comps = tuple(comps)
    if glob.endswith(".*"):
        b = tuple(glob[:-2].split(".")); return comps[:len(b)] == b
    if glob.endswith(".+"):
        b = tuple(glob[:-2].split(".")); return len(comps) > len(b) and comps[:len(b)] == b
    return comps == tuple(glob.split("."))

def lake_targets(root):
    cfg = tomllib.load(open(os.path.join(root, "lakefile.toml"), "rb"))
    libs = {}
    for lib in cfg.get("lean_lib", []):
        libs[lib["name"]] = lib.get("globs", [lib["name"]])
    exes = {e["name"]: {"srcDir": e.get("srcDir", "."), "root": e.get("root", e["name"])}
            for e in cfg.get("lean_exe", [])}
    return cfg, libs, exes

# ---------------------------------------------------------------- main
def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()

def main(root, out):
    root = os.path.abspath(root); os.makedirs(out, exist_ok=True)
    files = []
    for d, dirs, fs in os.walk(root):
        dirs[:] = sorted(x for x in dirs if x not in SKIP_DIRS)
        for f in sorted(fs):
            if f.endswith(".lean"):
                files.append(os.path.relpath(os.path.join(d, f), root).replace(os.sep, "/"))
    files.sort()

    cfg, libs, exes = lake_targets(root)
    exe_files = {f"{v['srcDir'].rstrip('/')}/{v['root'].replace('.', '/')}.lean".lstrip("./"): k
                 for k, v in exes.items()}

    entries, mod_of, errors = {}, {}, []
    for rel in files:
        p = os.path.join(root, rel)
        raw = open(p, "rb").read()
        text = raw.decode("utf-8")
        top = rel.split("/")[0]
        dclass = top if top in CORPUS_DIRS else ("root" if "/" not in rel else "other")
        if rel in exe_files:
            mod, comps = None, None
        else:
            comps = tuple(rel[:-5].split("/"))
            mod = render_name(comps)
            if mod in mod_of:
                errors.append({"file": rel, "error": f"module name collision with {mod_of[mod]}"})
            mod_of[mod] = rel
        try:
            hdr = parse_header(text); herr = None
        except HeaderError as e:
            hdr, herr = {"module": None, "prelude": None, "imports": []}, str(e)
            errors.append({"file": rel, "error": herr})
        entries[rel] = {"path": rel, "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
                        "lines": text.count("\n") + (0 if text.endswith("\n") or not text else 1),
                        "directory_class": dclass, "module_name": mod,
                        "module_components": list(comps) if comps else None,
                        "lean_module_system": hdr["module"], "prelude": hdr["prelude"],
                        "header_parse_error": herr, "imports": hdr["imports"],
                        "lexical": lexical_scan(text)}
        if rel in exe_files:
            entries[rel]["lake_exe"] = exe_files[rel]

    internal_roots = set(libs) | {entries[r]["module_components"][0] for r in mod_of.values()}
    graph, missing, external_roots = {}, [], {}
    for rel, e in entries.items():
        deps = []
        for imp in e["imports"]:
            m = imp["module"]; r = imp["module_components"][0]
            if m in mod_of:
                imp["resolution"] = "internal"; deps.append(m)
            elif r in internal_roots:
                imp["resolution"] = "missing-internal"
                missing.append({"importer": rel, "module": m})
            else:
                imp["resolution"] = "external-unresolved"  # needs Lean environment
                external_roots[r] = external_roots.get(r, 0) + 1
        graph[rel] = sorted(set(deps))

    # build closure of Lake targets
    def closure(seed_mods):
        seen, stack = set(), list(seed_mods)
        while stack:
            m = stack.pop()
            if m in seen or m not in mod_of: continue
            seen.add(m); stack.extend(graph[mod_of[m]])
        return seen
    default_targets = cfg.get("defaultTargets", [])
    test_lib = cfg.get("testDriver")
    target_of = {}
    for lib, globs in libs.items():
        seeds = [m for m, r in mod_of.items()
                 if any(glob_match(g, entries[r]["module_components"]) for g in globs)]
        for m in closure(seeds):
            target_of.setdefault(m, set()).add(lib)
    for exe, v in exes.items():
        rel = next(r for r, x in exe_files.items() if x == exe)
        if rel in entries:
            for m in closure(graph[rel]):
                target_of.setdefault(m, set()).add(f"exe:{exe}")
    for rel, e in entries.items():
        m = e["module_name"]
        tg = sorted(target_of.get(m, set())) if m else [f"exe:{e['lake_exe']}"]
        e["lake_targets"] = tg
        e["built_by_default"] = any(t in default_targets for t in tg)
        e["reachable"] = bool(tg)
    unreachable = sorted(r for r, e in entries.items() if not e["reachable"])

    # topological order (Kahn, lexicographic tie-break => deterministic)
    mods = sorted(mod_of)
    indeg = {m: 0 for m in mods}; rdeps = {m: [] for m in mods}
    for m in mods:
        for d in graph[mod_of[m]]:
            indeg[m] += 1; rdeps[d].append(m)
    import heapq
    ready = [m for m in mods if indeg[m] == 0]; heapq.heapify(ready); order = []
    while ready:
        m = heapq.heappop(ready); order.append(m)
        for r in rdeps[m]:
            indeg[r] -= 1
            if indeg[r] == 0: heapq.heappush(ready, r)
    cycle = sorted(m for m in mods if indeg[m] > 0)

    # aggregate
    by_class = {}
    for e in entries.values():
        by_class[e["directory_class"]] = by_class.get(e["directory_class"], 0) + 1
    tree_lines = "".join(f"{entries[r]['sha256']}  {r}\n" for r in files)
    summary = {
        "contract": "LEAN-M2-CC-001", "gate": "G1", "stage": "pre-elaboration",
        "inventory_schema": "1.1.0",
        "module_name_form": "Lean Name.toString rendering; non-identifier components wrapped in «»",
        "tool": "lean-m2/tools/g1_inventory.py", "tool_sha256": sha256_file(os.path.abspath(__file__)),
        "lean_files": len(files), "files_by_directory_class": dict(sorted(by_class.items())),
        "lean_module_system_files": sum(1 for e in entries.values() if e["lean_module_system"]),
        "non_module_files": sorted(r for r, e in entries.items() if e["lean_module_system"] is False),
        "header_parse_errors": errors,
        "internal_import_edges": sum(len(v) for v in graph.values()),
        "missing_internal_imports": missing,
        "external_import_roots": dict(sorted(external_roots.items())),
        "lake_default_targets": default_targets, "lake_test_driver": test_lib,
        "lake_libs": {k: v for k, v in sorted(libs.items())},
        "files_built_by_default": sum(1 for e in entries.values() if e["built_by_default"]),
        "unreachable_files": unreachable,
        "import_cycles": cycle,
        "source_tree_sha256": hashlib.sha256(tree_lines.encode()).hexdigest(),
        "source_tree_sha256_definition": "sha256 of sorted lines '<file sha256>  <relpath>\\n' over all inventoried .lean files",
        "lexical_totals_non_authoritative": {
            "sorry_tokens": sum(e["lexical"]["sorry_tokens"] for e in entries.values()),
            "decl_keyword_counts": dict(sorted({k: sum(e["lexical"]["decl_keyword_counts"].get(k, 0) for e in entries.values())
                                                for e0 in entries.values() for k in e0["lexical"]["decl_keyword_counts"]}.items())),
        },
        "not_established": [
            "external imports resolve (needs Lean v4.33.1 + Mathlib environment)",
            "declarations, namespaces, kinds, axioms, sorry (needs Lean environment; lexical counts are estimates)",
        ],
    }
    for e in entries.values():
        for imp in e["imports"]:
            imp.setdefault("resolution", "unparsed")

    def dump(name, obj):
        with open(os.path.join(out, name), "w", encoding="utf-8") as f:
            json.dump(obj, f, indent=1, sort_keys=True, ensure_ascii=False); f.write("\n")
    dump("inventory.json", {"summary": summary, "files": [entries[r] for r in files]})
    dump("imports.json", {"graph": {mod_of_rel(entries, r): [d for d in graph[r]] for r in files},
                          "topological_order": order, "cycles": cycle,
                          "missing_internal": missing, "external_roots": summary["external_import_roots"]})
    dump("source-hashes.json", {"source_tree_sha256": summary["source_tree_sha256"],
                                "files": {r: entries[r]["sha256"] for r in files}})
    with open(os.path.join(out, "source-tree.sha256"), "w") as f:
        f.write(tree_lines)
    return summary

def mod_of_rel(entries, rel):
    return entries[rel]["module_name"] or f"exe-root:{rel}"

if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit("usage: g1_inventory.py <lean-project-root> <out-dir>")
    s = main(sys.argv[1], sys.argv[2])
    blocked = s["header_parse_errors"] or s["missing_internal_imports"] or s["import_cycles"]
    print(json.dumps({k: s[k] for k in ("lean_files", "files_by_directory_class", "files_built_by_default",
                                        "internal_import_edges", "external_import_roots", "source_tree_sha256")},
                     indent=1, ensure_ascii=False))
    print(f"header_parse_errors={len(s['header_parse_errors'])} missing_internal={len(s['missing_internal_imports'])} "
          f"cycles={len(s['import_cycles'])} unreachable={len(s['unreachable_files'])} non_module={len(s['non_module_files'])}")
    print("G1-pre:", "BLOCKED" if blocked else "PASS (pre-elaboration only)")
    sys.exit(1 if blocked else 0)
