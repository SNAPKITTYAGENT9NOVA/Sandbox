<!-- SPDX-License-Identifier: AGPL-3.0-only -->
<!-- Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) -->
# LEAN-M2-CC-001: Lean 4 → Modula-2 mathematical library

This repository builds the pipeline that reconstructs a Lean 4 mathematical library as native
Modula-2. Computational definitions are extracted to C and compiled with CompCert. Lean proof
provenance is kept. The target is AArch64 Linux.

**Start here:** [`lean-m2/README.md`](lean-m2/README.md)

## Status

| Gate | What | State | Evidence |
|---|---|---|---|
| G0 | Toolchain probe: CompCert 3.18, gm2, Lean, linked ABI probe | **PASS** (toolchain-only), native AArch64 | CI `lean-m2 workstation (G0)` |
| G1 | Corpus inventory: hashes, Lean headers, import graph, Lake targets | **PASS**, Lean-native tool | `lean-m2/corpus.lock.yaml`, `EVIDENCE.sha256` |
| G2 | `lake build` + Lean-native declaration and axiom ledger | **PASS**: 17,232 constants; 12,390 `LEAN_VERIFIED`, 4,842 `BLOCKED` | `lean-m2/corpus/formal-conjectures/84cf7f8/g2-headline.json` |
| G3–G6 | Extraction → CompCert → Modula-2 → differential test | **MathIR v9 generator PASS**: 218 of 411 `ℕᵏ→ℕ / Prop / Bool` definitions generated as CompCert C + native Modula-2 (loops, sums/products/counts/maxima/lcm over ranges, divisors, primes and images, predicates and Bool, number-theory and digit builtins, checked ℤ subterms, exact ℚ subterms, decidable predicates with bounded quantifiers, prime-factor and digit lists, range-based lists, `let`, lookback recursion); 0 unsound and 0 incomplete in 22,171 cases (exact wide fallback when 64 bits overflow); SLICE-001 acceptance passes on generated code. **Release gate PASS** (39 fail-closed checks; packaged by `lean-m2-release.yml`) | `lean-m2/g3/gen/LEDGER.json` |

**Corpus:** [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
@ `84cf7f8` (1,777 `.lean` files, Lean 4.33.1, Mathlib v4.33.1).

**The Modula-2 library has 218 generated functions so far** (MathIR v9), plus the hand-written SLICE-001. The rest is the pipeline.
`LEAN_VERIFIED` means Lean's kernel accepted the declaration using only `propext`,
`Classical.choice` and `Quot.sound`. It says nothing about any translation.

## Layout

```
lean-m2/
  toolchain.lock.yaml     frozen contract lockfile (fully measured; re-checked by the release gate)
  corpus.lock.yaml        corpus commit, hashes, dependency pins, G1/G2 results
  workstation.lock.yaml   container image pins (CompCert source commit, Coq, OCaml)
  corpus/…/84cf7f8/       EVIDENCE.sha256 (pins regenerated inventory), g2-headline.json
  docker/                 AArch64 toolchain image
  scripts/                G0 probe, CI annotation helper
  tools/                  G1 inventory (Lean), G2 ledger (Lean), G2 summarizer (Python glue)
  fixtures/abi/           CompCert-C <-> gm2 ABI probe
  workstation/            Windows (PowerShell) and Linux/macOS launchers
.github/workflows/        lean-m2-workstation (G0, ARM), lean-m2-g1, lean-m2-g2
```

## History

This is a fork of [jamiedevera/Sandbox](https://github.com/jamiedevera/Sandbox), a Next.js web app
whose original README stated MIT licensing. The app and its leftovers were removed. They remain in
git history and upstream.

## License

AGPL-3.0-only (`LICENSE`). Every source file carries an SPDX header; JSON data files are covered by `REUSE.toml`.
The translated definitions come from google-deepmind/formal-conjectures (Apache-2.0).
