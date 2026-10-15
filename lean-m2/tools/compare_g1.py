#!/usr/bin/env python3
"""Differential check: Python G1 inventory (schema 1.1.0) vs Lean G1 inventory (schema 2.0.0).

Usage: python3 -I compare_g1.py <python-out-dir> <lean-out-dir>
Compares semantics, not bytes (the two serializers format JSON differently). Exit 1 on any
difference; prints the first differences found. Used once, to retire the Python implementation.
"""
import json, sys

def load(d):
    return (json.load(open(f"{d}/inventory.json")), json.load(open(f"{d}/imports.json")))

def main(pyd, led):
    (pinv, pimp), (linv, limp) = load(pyd), load(led)
    diffs = []
    def chk(what, a, b):
        if a != b and len(diffs) < 40:
            diffs.append(f"{what}: python={json.dumps(a, ensure_ascii=False)[:200]} lean={json.dumps(b, ensure_ascii=False)[:200]}")
    pf = {f["path"]: f for f in pinv["files"]}; lf = {f["path"]: f for f in linv["files"]}
    chk("file set", sorted(pf), sorted(lf))
    for path in sorted(set(pf) & set(lf)):
        p, l = pf[path], lf[path]
        for k_py, k_le in [("sha256", "sha256"), ("bytes", "bytes"), ("directory_class", "directory_class"),
                           ("module_components", "module_components"), ("lean_module_system", "lean_module_system"),
                           ("prelude", "prelude"), ("header_parse_error", "header_parse_error"),
                           ("lake_targets", "lake_targets"), ("built_by_default", "built_by_default"),
                           ("reachable", "reachable")]:
            chk(f"{path}:{k_py}", p.get(k_py), l.get(k_le))
        pi = [(i["module_components"], i["all"], "meta" in i["modifiers"], i["resolution"]) for i in p["imports"]]
        li = [(i["module_components"], i["import_all"], i["is_meta"], i["resolution"]) for i in l["imports"]]
        chk(f"{path}:imports(components,all,meta,resolution)", pi, li)
        # rendering is compared separately: it is presentation, components are identity
        chk(f"{path}:module_name rendering", p.get("module_name"), l.get("module_name"))
    ps, ls = pinv["summary"], linv["summary"]
    for k in ["lean_files", "files_by_directory_class", "internal_import_edges", "external_import_roots",
              "files_built_by_default", "unreachable_files", "import_cycles", "source_tree_sha256",
              "non_module_files", "lake_default_targets", "lake_test_driver", "lake_libs"]:
        chk(f"summary.{k}", ps.get(k), ls.get(k))
    chk("summary.missing_internal_imports(count)", len(ps["missing_internal_imports"]), len(ls["missing_internal_imports"]))
    chk("summary.header_parse_errors(count)", len(ps["header_parse_errors"]), len(ls["header_parse_errors"]))
    chk("imports.topological_order", pimp["topological_order"], limp["topological_order"])
    print(f"files compared: {len(set(pf) & set(lf))}; differences: {len(diffs)}{' (first 40)' if len(diffs) >= 40 else ''}")
    for d in diffs: print("DIFF", d)
    print("G1 differential:", "IDENTICAL" if not diffs else "DIFFERENT")
    return 0 if not diffs else 1

if __name__ == "__main__":
    sys.exit(main(*sys.argv[1:3]))
