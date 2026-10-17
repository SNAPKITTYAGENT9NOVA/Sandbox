#!/usr/bin/env python3
"""LEAN-M2-CC-001 release gate (G6): fail-closed verification and packaging.

Every check is recorded as PASS or BLOCKED in gate-report.txt. The release package is written
only if every check passes; otherwise the script exits 1 and nothing is packaged (the report and
inputs are retained by the workflow). Nothing is assumed: each check reads evidence produced by
the same workflow run, or a frozen lockfile in the repository.

usage: gate.py --repo <lean-m2 dir> --lean <MathIR lean-job evidence dir> --arm <MathIR arm-job out dir>
               --observed <measure-toolchain.sh output> --version <v> --commit <sha> --run <run id>
               --dist <output dir>
"""
import argparse, hashlib, json, os, re, shutil, sys, tarfile, io

import yaml

ap = argparse.ArgumentParser()
for a in ("repo", "lean", "arm", "observed", "version", "commit", "run", "dist"):
    ap.add_argument("--" + a, required=True)
A = ap.parse_args()

checks = []
def check(name, ok, detail):
    checks.append(("PASS" if ok else "BLOCKED", name, detail))
    return ok

def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

def read(path):
    try:
        with open(path, encoding="utf-8") as f:
            return f.read()
    except OSError:
        return None

def dig(d, dotted):
    for k in dotted.split("."):
        if not isinstance(d, dict) or k not in d:
            return None
        d = d[k]
    return d

def walk(d, prefix=""):
    if isinstance(d, dict):
        for k, v in d.items():
            yield from walk(v, f"{prefix}{k}.")
    else:
        yield prefix[:-1], d

repo, lean, arm = A.repo, A.lean, A.arm
tool = yaml.safe_load(read(os.path.join(repo, "toolchain.lock.yaml")) or "") or {}
corpus = yaml.safe_load(read(os.path.join(repo, "corpus.lock.yaml")) or "") or {}
ledger_txt = read(os.path.join(repo, "g3/gen/LEDGER.json"))
ledger = json.loads(ledger_txt) if ledger_txt else {}

# ---- 1. contract lockfile: complete, and the measured toolchain matches it ----
required = [k for k, v in walk(tool) if v == "REQUIRED"]
check("toolchain.lock complete", not required, "unmeasured: " + ", ".join(required) if required else "no REQUIRED fields")
check("contract fail_closed", dig(tool, "contract.fail_closed") is True, f"contract.fail_closed = {dig(tool, 'contract.fail_closed')}")
check("release policy", dig(tool, "release.require_all_mandatory_gates") is True and dig(tool, "release.allow_unverified_as_verified") is False,
      "require_all_mandatory_gates and not allow_unverified_as_verified")
obs = {}
for line in (read(A.observed) or "").splitlines():
    if "\t" in line:
        k, v = line.split("\t", 1)
        obs[k] = v
check("toolchain measured", len(obs) >= 13, f"{len(obs)} fields measured")
for k, v in sorted(obs.items()):
    locked = dig(tool, k)
    check(f"toolchain {k}", locked is not None and str(locked) == v, f"locked={locked!r} observed={v!r}")
lake = (read(os.path.join(lean, "lake-version.txt")) or "").strip().splitlines()
lake = lake[0] if lake else ""
check("toolchain lean.lake_version", lake != "" and str(dig(tool, "lean.lake_version")) == lake,
      f"locked={dig(tool, 'lean.lake_version')!r} observed={lake!r}")

# ---- 2. corpus gates G1 / G2 ----
g1 = dig(corpus, "corpus.g1_status") or {}
check("G1 corpus inventory", bool(g1) and all(v == "PASS" for v in g1.values()), json.dumps(g1))
check("G2 Lean validation", dig(corpus, "corpus.g2_status.lake_build_exit") == 0,
      f"lake_build_exit = {dig(corpus, 'corpus.g2_status.lake_build_exit')}")
check("corpus commit", ledger.get("corpus_commit") == dig(corpus, "corpus.commit"),
      f"ledger {ledger.get('corpus_commit')} vs corpus.lock {dig(corpus, 'corpus.commit')}")

# ---- 3. MathIR extraction (lean job of this run) ----
mlog = read(os.path.join(lean, "mathir.log")) or ""
m = re.search(r"MATHIR candidates=(\d+) translated=(\d+) blocked=(\d+) cases=(\d+) .*ir_fidelity_mismatches=(\d+)", mlog)
check("MathIR summary present", m is not None, m.group(0) if m else "no MATHIR summary in mathir.log")
if m:
    cand, trans, blk, cases, fid = map(int, m.groups())
    cov = ledger.get("coverage", {})
    check("fidelity", fid == 0, f"IR vs Lean compiled definitions: {fid} mismatches")
    check("coverage = ledger", (trans, blk) == (cov.get("translated"), cov.get("blocked")),
          f"run {trans}/{blk} vs ledger {cov.get('translated')}/{cov.get('blocked')}")
    check("reference cases = ledger", cases == ledger.get("evidence", {}).get("reference_cases"),
          f"run {cases} vs ledger {ledger.get('evidence', {}).get('reference_cases')}")
gen = os.path.join(lean, "gen")
sums = read(os.path.join(lean, "gen.sha256")) or ""
bad = [f for h, f in (l.split(None, 1) for l in sums.splitlines() if l.strip())
       if not os.path.exists(os.path.join(gen, f.strip())) or sha(os.path.join(gen, f.strip())) != h]
check("generated sources", sums != "" and not bad, f"{len(sums.splitlines())} files; mismatched: {bad}")

# ---- 4. CompCert / gm2 build and differential tests (arm job of this run) ----
gt = read(os.path.join(arm, "gen-test.log")) or ""
acc = read(os.path.join(arm, "acceptance.log")) or ""
check("differential PASS", "MATHIR DIFFERENTIAL: PASS (sound on every case)" in gt, "gen-test.log")
for lang in ("C", "M2"):
    mm = re.search(rf"MATHIR {lang}:\s+unsound=(\d+) incomplete=(\d+)", gt)
    check(f"{lang} sound and complete", mm is not None and mm.groups() == ("0", "0"),
          mm.group(0) if mm else f"no MATHIR {lang} line")
fm = re.search(r"MATHIR functions=(\d+) cases=(\d+)", gt)
check("tested = translated", fm is not None and m is not None and int(fm.group(1)) == trans and int(fm.group(2)) == cases,
      fm.group(0) if fm else "no MATHIR functions line")
check("acceptance (SLICE-001 on generated code)", "SLICE001 DIFFERENTIAL: PASS" in acc, "acceptance.log")
blog = read(os.path.join(arm, "build.log")) or ""
built = dict(re.findall(r"^(\S+) machine=(\S+) sha256=", blog, re.M))
want = ledger.get("evidence", {}).get("objects_sha256", {})
check("objects recorded in ledger", bool(want), f"{len(want)} objects")
for name, h in sorted(want.items()):
    p = os.path.join(arm, name)
    got = sha(p) if os.path.exists(p) else None
    check(f"object {name}", built.get(name) == "AArch64" and got == h,
          f"machine={built.get(name)} sha256={got} ledger={h}")

# ---- report; package only if everything passed ----
os.makedirs(A.dist, exist_ok=True)
ok = all(s == "PASS" for s, _, _ in checks)
report = "".join(f"{s}\t{n}\t{d}\n" for s, n, d in checks)
report += f"GATE {'PASS' if ok else 'BLOCKED'}: {sum(s == 'PASS' for s, _, _ in checks)}/{len(checks)} checks passed\n"
with open(os.path.join(A.dist, "gate-report.txt"), "w") as f:
    f.write(report)
sys.stdout.write(report)
if not ok:
    sys.exit(1)

name = f"lean-m2-{A.version}-aarch64-linux"
root = os.path.join(A.dist, name)
shutil.rmtree(root, ignore_errors=True)
layout = {
    "include": [(gen, "lm2_gen.h"), (os.path.join(repo, "g3/gen/runtime"), "lm2_nat.h"), (os.path.join(repo, "g3/gen/runtime"), "lm2_wide.h")],
    "src/c": [(gen, "lm2_gen.c")],
    "src/m2": [(gen, "LM2Gen.def"), (gen, "LM2Gen.mod"), (gen, "lm2_gen_bind.def")] +
              [(os.path.join(repo, "g3/gen/runtime"), f) for f in ("LM2Nat.def", "LM2Nat.mod", "LM2Wide.def", "LM2Wide.mod")],
    "lib/aarch64-linux": [(arm, f) for f in ("lm2_gen.o", "LM2Gen.o", "LM2Nat.o", "LM2Wide.o")],
    "evidence": [(os.path.join(repo, "g3/gen"), "LEDGER.json"), (gen, "mathir.json"), (gen, "report.txt"), (gen, "blocked.txt"),
                 (arm, "gen-test.log"), (arm, "acceptance.log"), (arm, "build.log"),
                 (repo, "toolchain.lock.yaml"), (repo, "corpus.lock.yaml"),
                 (os.path.join(repo, "corpus/formal-conjectures/84cf7f8"), "g2-headline.json")],
    "": [(os.path.join(repo, "release"), "README.md"), (os.path.join(repo, "release"), "NOTICE")],
}
for sub, files in layout.items():
    d = os.path.join(root, sub)
    os.makedirs(d, exist_ok=True)
    for src, f in files:
        shutil.copyfile(os.path.join(src, f), os.path.join(d, f))
shutil.copyfile(A.observed, os.path.join(root, "evidence", "toolchain.observed.tsv"))
shutil.copyfile(os.path.join(A.dist, "gate-report.txt"), os.path.join(root, "evidence", "gate-report.txt"))

files = sorted(os.path.relpath(os.path.join(dp, f), root) for dp, _, fs in os.walk(root) for f in fs)
manifest = {
    "contract": "LEAN-M2-CC-001",
    "package": name,
    "version": A.version,
    "source_commit": A.commit,
    "ci_run": int(A.run),
    "target": {"architecture": "AArch64", "os": "Linux", "c_compiler": f"CompCert {dig(tool, 'compcert.version')}",
               "modula2_compiler": f"gm2 {dig(tool, 'modula2.version')}"},
    "corpus": {"repository": dig(corpus, "corpus.repository"), "commit": dig(corpus, "corpus.commit"),
               "license": dig(corpus, "corpus.license")},
    "coverage": {"candidates": cand, "translated": trans, "blocked": blk},
    "evidence": {"reference_cases": cases, "fidelity_mismatches": fid, "unsound": 0, "incomplete": 0,
                 "acceptance": "SLICE-001 PASS", "gate_checks": len(checks)},
    "statuses_per_function": ledger.get("statuses_per_translated_function"),
    "not_claimed": ledger.get("not_claimed"),
    "limits": ledger.get("limits"),
    "files_sha256": {f: sha(os.path.join(root, f)) for f in files},
}
with open(os.path.join(root, "MANIFEST.json"), "w") as f:
    json.dump(manifest, f, indent=2, ensure_ascii=False)
    f.write("\n")

# deterministic tarball: sorted entries, fixed owner, mode and mtime
tgz = os.path.join(A.dist, name + ".tar.gz")
entries = sorted(os.path.relpath(os.path.join(dp, f), A.dist) for dp, _, fs in os.walk(root) for f in fs)
with open(tgz, "wb") as raw:
    import gzip
    with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0, filename="") as gz:
        with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
            for rel in entries:
                ti = tar.gettarinfo(os.path.join(A.dist, rel), arcname=rel)
                ti.uid = ti.gid = 0; ti.uname = ti.gname = ""; ti.mtime = 0; ti.mode = 0o644
                with open(os.path.join(A.dist, rel), "rb") as fh:
                    tar.addfile(ti, fh)
with open(os.path.join(A.dist, "SHA256SUMS"), "w") as f:
    f.write(f"{sha(tgz)}  {os.path.basename(tgz)}\n")
print(f"PACKAGED {os.path.basename(tgz)} sha256={sha(tgz)} files={len(files)}")
