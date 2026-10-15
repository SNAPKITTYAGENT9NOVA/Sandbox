#!/usr/bin/env python3
"""LEAN-M2-CC-001 · G2 summarizer.

Usage:
  python3 -I g2_summarize.py --inventory INV.json --ledger LEDGER.jsonl \
      --build-exit N --test-exit N [--problems PROBLEMS.json] --out DIR

Maps raw Lean evidence to contract statuses. The policy is explicit and conservative:

  STANDARD_AXIOMS = {propext, Classical.choice, Quot.sound}

  LEAN_VERIFIED  <=> lake build exited 0
                     AND the constant's transitive axioms are a subset of STANDARD_AXIOMS
                     (in particular: no sorryAx, no corpus-local axiom).
  BLOCKED        otherwise, with a reason (depends_on_sorry / nonstandard_axioms / build_failed).

  G3 extraction candidates (planning only — NOT a translation claim):
     kind == def, safety == safe, not noncomputable, not internal,
     LEAN_VERIFIED, no extern / implemented_by.

Outputs: g2-result.json (summary), verification-ledger.jsonl (one status row per constant).
"""
import argparse, collections, json, os, re, sys

# Compiler-generated auxiliaries that are not user definitions (e.g. `foo.match_1`).
AUX_LAST_COMPONENT = re.compile(r"(match|proof|eq|fun|lambda|spec|sunfold|unfold)_\d+$")

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Exact, computable domains admissible for the first extraction slices (G3). Anything else in a
# candidate's type (ℝ, Set, Finset, typeclass structures, ...) excludes it for now.
EXACT_DOMAIN_CONSTS = {"Nat", "Int", "Bool", "List", "Fin", "Prod", "Option", "Unit", "PUnit",
                       "Sum", "UInt8", "UInt16", "UInt32", "UInt64", "Char", "String", "Array"}

def axiom_family(name):
    """Group non-standard axioms. Lean introduces one auxiliary axiom per `native_decide` /
    `decide +native` use (name contains `._native.`); these trust the compiled evaluator, not
    the kernel. Everything else is reported by name."""
    if "._native.native_decide.ax_" in name: return "native_decide (compiler-trusted, auxiliary)"
    if "._native.decide.ax_" in name: return "decide +native (compiler-trusted, auxiliary)"
    if "._native." in name: return "other ._native. (compiler-trusted, auxiliary)"
    if name in ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler"): return name + " (compiler trust)"
    return name

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--inventory", required=True)
    ap.add_argument("--ledger", required=True)
    ap.add_argument("--build-exit", type=int, required=True)
    ap.add_argument("--test-exit", type=int, required=True)
    ap.add_argument("--problems")
    ap.add_argument("--expected-modules", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)

    inv = json.load(open(a.inventory))
    # Join on component tuples, never on dotted strings (components may contain '.').
    cls_of = {tuple(f["module_components"]): f["directory_class"] for f in inv["files"] if f["module_components"]}
    expected = [tuple(l.rstrip("\n").split("\t")[1:]) for l in open(a.expected_modules) if l.strip()]

    build_ok = a.build_exit == 0
    by = collections.defaultdict(collections.Counter)
    by_dir_ni = collections.defaultdict(collections.Counter)
    reason_totals = collections.Counter()
    other_dependents = []
    axiom_sets = collections.Counter()
    nonstd_axioms = collections.Counter()
    seen_modules = set()
    rows = 0
    candidates = []
    with open(a.ledger) as f, open(os.path.join(a.out, "verification-ledger.jsonl"), "w") as vo:
        for line in f:
            r = json.loads(line); rows += 1
            mkey = tuple(r["module_components"])
            seen_modules.add(mkey)
            axs = set(r["axioms"])
            cls = cls_of.get(mkey, "unknown")
            reasons = []
            if not build_ok: reasons.append("build_failed")
            if "sorryAx" in axs: reasons.append("depends_on_sorry")
            other = sorted(axs - STANDARD_AXIOMS - {"sorryAx"})
            if other: reasons.append("nonstandard_axioms")
            for fam in {axiom_family(x) for x in other}: nonstd_axioms[fam] += 1
            status = "LEAN_VERIFIED" if not reasons else "BLOCKED"
            key = f"{cls}/{r['kind']}"
            by[key][status] += 1
            for x in reasons: reason_totals[x] += 1
            if not r["internal"]:
                by_dir_ni[f"{cls}/{r['kind']}"][status] += 1
            if not r["internal"]:
                axiom_sets[",".join(sorted(axs)) or "(none)"] += 1
            cand = (r["kind"] == "def" and r["safety"] == "safe" and not r["noncomputable"]
                    and not r["internal"] and status == "LEAN_VERIFIED"
                    and not r["extern"] and r["implemented_by"] is None)
            if cand:
                exact = (not r.get("returns_prop", True)
                         and not r.get("returns_sort", True)          # Type-valued: a type former
                         and not AUX_LAST_COMPONENT.search(r["name"])  # match_N etc.
                         and set(r.get("type_consts", ["?"])) <= EXACT_DOMAIN_CONSTS)
                candidates.append({"name": r["name"], "module": r["module"], "directory_class": cls,
                                   "type": r.get("type_pp"), "type_consts": r.get("type_consts"),
                                   "returns_prop": r.get("returns_prop"), "exact_domain": exact})
            if other and not all(axiom_family(x) != x for x in other):
                other_dependents.append({"name": r["name"], "module": r["module"],
                                         "axioms": [x for x in other if axiom_family(x) == x]})
            vo.write(json.dumps({"name": r["name"], "module": r["module"], "directory_class": cls,
                                 "kind": r["kind"], "statuses": [status], "reasons": reasons,
                                 "axioms": sorted(axs), "g3_extraction_candidate": cand},
                                sort_keys=True) + "\n")

    missing = [".".join(m) for m in sorted(set(expected) - seen_modules)]
    # A module with zero constants would also be "missing" from seen_modules; the ledger
    # itself throws on modules absent from the environment, so here we only report.
    problems = None
    if a.problems and os.path.exists(a.problems):
        p = json.load(open(a.problems))["problems"]
        problems = {
            "count": len(p),
            "by_category": dict(collections.Counter(x["category"] for x in p).most_common()),
            "has_sorry_free_proof": sum(1 for x in p if x.get("hasSorryFreeProof")),
            "source": "corpus tool scripts/extract_names.lean (repository metadata, not re-derived)",
        }
    with open(os.path.join(a.out, "g3-extraction-candidates.json"), "w") as f:
        json.dump(sorted(candidates, key=lambda c: (c["module"], c["name"])), f, indent=1, sort_keys=True)

    status = "PASS" if build_ok and rows > 0 else "BLOCKED"
    result = {
        "contract": "LEAN-M2-CC-001", "gate": "G2", "status": status,
        "policy": {"standard_axioms": sorted(STANDARD_AXIOMS),
                   "lean_verified_requires": "build exit 0 and transitive axioms subset of standard_axioms"},
        "lake_build_exit": a.build_exit,
        "lake_test_exit_recorded_not_gating": a.test_exit,
        "ledger_rows": rows,
        "modules_expected": len(expected), "modules_with_constants": len(seen_modules),
        "modules_without_constants": missing,
        "status_by_directory_and_kind": {k: dict(v) for k, v in sorted(by.items())},
        "top_axiom_sets_non_internal": dict(axiom_sets.most_common(12)),
        "nonstandard_axiom_families_by_dependent_constants": dict(nonstd_axioms.most_common()),
        "status_totals": dict(sum((collections.Counter(v) for v in by.values()), collections.Counter())),
        "reason_totals": dict(reason_totals),
        "status_by_directory_non_internal": {k: dict(v) for k, v in sorted(by_dir_ni.items())},
        "g3_extraction_candidates": len(candidates),
        "g3_candidates_by_directory": dict(collections.Counter(c["directory_class"] for c in candidates)),
        "corpus_problem_metadata": problems,
        "scope_note": ("LEAN_VERIFIED is per-constant kernel acceptance under the recorded axioms. "
                       "It says nothing about translation, extraction or Modula-2."),
    }
    json.dump(result, open(os.path.join(a.out, "g2-result.json"), "w"), indent=1, sort_keys=True)
    headline = {k: result[k] for k in ("status", "lake_build_exit", "ledger_rows", "modules_expected",
                "modules_with_constants", "status_totals", "reason_totals",
                "nonstandard_axiom_families_by_dependent_constants", "g3_extraction_candidates",
                "g3_candidates_by_directory", "corpus_problem_metadata")}
    headline["modules_without_constants_count"] = len(missing)
    headline["modules_without_constants"] = missing
    headline["non_family_nonstandard_axiom_dependents"] = other_dependents[:20]
    exact = [c for c in candidates if c["exact_domain"]]
    headline["g3_exact_domain_candidates"] = len(exact)
    headline["g3_exact_domain_by_directory"] = dict(collections.Counter(c["directory_class"] for c in exact))
    with open(os.path.join(a.out, "g3-exact-domain-candidates.txt"), "w") as f:
        for c in sorted(exact, key=lambda c: (c["module"], c["name"])):
            f.write(f"{c['name']} : {(c['type'] or '').replace(chr(10), ' ')[:160]}\n")
    headline["status_by_directory_non_internal"] = result["status_by_directory_non_internal"]
    json.dump(headline, open(os.path.join(a.out, "g2-headline.json"), "w"), indent=1, sort_keys=True)
    print(json.dumps(headline, indent=1, sort_keys=True))
    sys.exit(0 if status == "PASS" else 1)

if __name__ == "__main__":
    main()
