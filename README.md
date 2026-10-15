# Sandbox → LEAN-M2-CC-001 workstation

This repository now hosts the workstation toolchain for **LEAN-M2-CC-001**: reconstructing a
Lean 4 mathematical library as Modula-2, with CompCert-gated C extraction, on AArch64 Linux.

**Start here:** [`lean-m2/README.md`](lean-m2/README.md)

## Status

| Gate | What | State |
|---|---|---|
| G0 | Toolchain probe (CompCert 3.18, gm2, Lean, ABI link probe) | implemented; first native AArch64 run in CI |
| G1–G6 | Inventory, Lean validation, extraction, CompCert build, Modula-2, release | not implemented |

Nothing in this repository is a verified library yet. See the verification ledger rules in the contract.

## History

This is a fork of [jamiedevera/Sandbox](https://github.com/jamiedevera/Sandbox), a Next.js
deployment-risk analysis web app whose original README stated MIT licensing. The web app
(React UI, API route, WatsonX glue, its tests and CI) and its leftovers (`bob_sessions/`,
`TestCases/`, `BOB_DEVELOPMENT.md`) were removed from this fork. They remain in git history
and upstream.
