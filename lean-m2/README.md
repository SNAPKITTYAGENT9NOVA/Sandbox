# lean-m2: LEAN-M2-CC-001 pipeline

This folder holds the pipeline that reconstructs the Lean 4 corpus below as native Modula-2.
Eligible computational definitions are extracted to a C subset and compiled with CompCert 3.18
for AArch64 Linux. The pipeline runs as fail-closed gates G0–G6. Each gate writes
machine-readable evidence and blocks on anything unmeasured.

| Gate | State | Where the evidence lives |
|---|---|---|
| **G0** toolchain probe | **PASS** (`TOOLCHAIN_ONLY_PASS`), native AArch64 CI | `lean-m2 workstation (G0)` run annotations |
| **G1** corpus inventory | **PASS** (pre-elaboration), Lean-native tool | `corpus.lock.yaml`, `corpus/…/EVIDENCE.sha256`, `lean-m2 G1` runs |
| **G2** Lean validation and axiom ledger | **PASS** | `corpus/formal-conjectures/84cf7f8/g2-headline.json`, `corpus.lock.yaml` |
| **G3** extraction to C | 339 exact-domain candidates; **SLICE-001 done** (hand-written from the semantic contract, not yet auto-generated) | `g3/slice001/LEDGER.json` |
| **G4** CompCert build | **PASS for SLICE-001** (ccomp 3.18, AArch64 ELF) | `g3/slice001/LEDGER.json` |
| **G5** Modula-2 | **PASS for SLICE-001** (native module + C binding, gm2 13.3.0 ISO) | `g3/slice001/LEDGER.json` |
| **G6** differential testing and release | **SLICE-001: 2,511 cases, 0 failures**; release gate not built | `lean-m2 SLICE-001` runs |

## Frozen corpus

[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
@ `84cf7f8adfb0ea8d14c7d00bdf145cc9032bdf88` (Apache-2.0). It pins Lean `v4.33.1` and Mathlib
`v4.33.1`. It is a conjecture-statement benchmark: many statements are deliberately `sorry`.

| Directory | `.lean` files | Role |
|---|---|---|
| `FormalConjectures/` | 1515 | conjecture statements |
| `FormalConjecturesForMathlib/` | 225 | supporting definitions and results |
| `FormalConjecturesUtil/` | 22 | elaboration / utility code |
| `FormalConjecturesTest/` | 12 | tooling tests (test driver only) |
| root + `scripts/` | 3 | library roots, `extract_names` executable |
| **total** | **1777** | source tree sha256 `66015949…09d9` |

- **Imports:** 2,638 import declarations: 2,080 internal edges and 558 external (Mathlib 531, Lean 18, Batteries 5, Qq 3, Init 1).
- **Graph:** no missing internal imports and no cycles.
- **Dependencies:** Mathlib and the other Lake dependencies are pinned in `corpus.lock.yaml`. They are not part of the corpus.
- **Inventory:** regenerated, not stored. `corpus/formal-conjectures/84cf7f8/EVIDENCE.sha256` pins the exact bytes, and CI fails if a regeneration differs.

## G2 results (run 38653926670, Lean 4.33.1 `819816b`, `always_true` build variant)

| | |
|---|---|
| `lake build` / `lake test` / `extract_names` | exit 0 / 0 / 0 |
| Constants in the ledger | 17,232 across 1,750 modules |
| `LEAN_VERIFIED` | 12,390: kernel-checked, axioms within {`propext`, `Classical.choice`, `Quot.sound`} |
| `BLOCKED` | 4,842: 3,974 depend on `sorry`; 871 on non-standard axioms |
| Non-standard axiom families | `native_decide` 583, `decide +native` 289, `lcProof` 1 |
| Corpus metadata (`extract_names`) | 1,454 research-open and 2,410 research-solved statements, matching the project's published figures |

**Caveats:**
- **Build variant:** in the default `always_true` build, a Prop-valued `answer(sorry)` elaborates to `True`. The `postpone` variant has not been ledgered yet.
- **`native_decide` / `decide +native`:** these proofs trust Lean's compiled evaluator rather than the kernel, so they are deliberately **not** `LEAN_VERIFIED`.

## Tools

| Tool | Gate | Notes |
|---|---|---|
| `scripts/probe-toolchain.sh` | G0 | fail-closed toolchain checks and linked ABI probe |
| `tools/G1Inventory.lean` | G1 | Uses Lean's own `Parser.parseHeader` and `HeaderSyntax.imports`, Lake's own `Lake.Toml.loadToml`, and a FIPS 180-4 SHA-256 (passes the 5 NIST vectors; every file hash matches `sha256sum`). It replaced the Python G1 after a semantic differential over all 1,777 files reported IDENTICAL (run 38678453308) |
| `tools/g2_ledger_body.lean` | G2 | per-constant kind, safety, escape hatches, direct `sorry`, transitive axioms, and type facts for G3 |
| `tools/g2_summarize.py` | G2/G3 | maps the evidence to contract statuses, and filters the G3 exact-domain candidates |
| `scripts/annotate.sh` | CI | publishes evidence as check-run annotations, readable via the REST API |

## Toolchain image (`docker/Dockerfile`, `linux/arm64`)

| Component | Pin |
|---|---|
| Base | `ubuntu:24.04` (digest: REQUIRED in `workstation.lock.yaml`) |
| CompCert | commit `8135de0`: tag `v3.18` plus upstream's VERSION-only fix (the tagged commit reports 3.17). The build verifies that the diff is exactly `VERSION` |
| Coq / OCaml | Coq 8.20.1, OCaml 4.14.2 (opam) |
| GNU Modula-2 | Ubuntu noble `gm2`; exact version recorded by G0 |
| Lean / Lake | elan; the toolchain is chosen by each project's `lean-toolchain` |

CompCert is distributed under a non-commercial license by INRIA/AbsInt. Check that your use is permitted.

**ABI rules established on native AArch64:**
- No structs or unions are passed or returned by value.
- A `DEFINITION MODULE FOR "C"` needs `EXPORT UNQUALIFIED`. Without it, gm2 emits module-qualified symbols (`mod_proc`) and the link fails.

## Windows workstation (Docker Desktop)

Data lives on **D:** by default (`D:\lean-m2\{work,results,elan-toolchains}`).

```powershell
cd Sandbox\lean-m2\workstation
.\lean-m2.ps1 setup                  # pull the CI-built image (or: setup -Build)
.\lean-m2.ps1 info                   # shows native vs emulated
.\lean-m2.ps1 probe                  # G0, toolchain only
.\lean-m2.ps1 probe -Project <name>  # full G0 against D:\lean-m2\work\<name>
.\lean-m2.ps1 shell                  # bash in the container, D:\lean-m2\work at /work
```

- **ARM64 Windows:** the container runs natively.
- **x64 Windows:** it runs under QEMU. G0 **blocks** unless you pass `-AllowEmulation`, which records QEMU as part of the trusted base. Building the image under emulation takes hours, so prefer `setup` (pull).
- **Disk:** Docker Desktop keeps its disk image on C: unless you move it in its settings.

Linux/macOS: `workstation/lean-m2.sh` has the same commands. VS Code: `.devcontainer/lean-m2/`.

## CI

| Workflow | Runner | Does |
|---|---|---|
| `lean-m2-workstation.yml` | `ubuntu-24.04-arm` | builds the image, runs G0, and publishes `ghcr.io/snapkittyagent9nova/lean-m2-workstation` from `main` |
| `lean-m2-g1.yml` | `ubuntu-latest` | Lean G1: SHA-256 self-test, every hash vs `sha256sum`, and output vs `EVIDENCE.sha256` |
| `lean-m2-g2.yml` | `ubuntu-latest` | re-verifies the corpus, then runs `lake build`, the ledger and the summary. Corpus build cache is saved |

All three publish their key evidence as check-run annotations, and upload full evidence as artifacts.

## Lockfiles

- `toolchain.lock.yaml`: the frozen contract lockfile (schema 1.0.0). `REQUIRED` fields are blockers until measured.
- `corpus.lock.yaml`: corpus commit, file hashes, dependency pins, per-directory tree hashes, and the G1/G2 status and open items.
- `workstation.lock.yaml`: image pins, with the rationale for the CompCert pin.

## Open items

- Ledger the `postpone` build variant.
- Record the base-image and published-image digests.
- Generalize SLICE-001's hand-written C and Modula-2 into a MathIR-driven generator (G3/G5), then expand slice by slice through the 339 candidates.

Resolved:
- **The `lcProof` dependent** is a compiler-generated `unsafe` auxiliary (`Nat.primeFactorsEq.unsafe_1`).
- **The 14 modules with no constants** are 2 aggregator roots, 11 stub files and 1 attribute-only file.
