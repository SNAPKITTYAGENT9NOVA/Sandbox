# lean-m2 — LEAN-M2-CC-001 workstation

A reproducible AArch64 Linux toolchain environment for the Lean 4 → Modula-2 mathematical
library pipeline, with CompCert-gated extraction. It covers **gate G0 (toolchain probe)** of
contract `LEAN-M2-CC-001`. G1–G6 (inventory, Lean validation, extraction, CompCert
build, Modula-2 generation, differential release) are **not implemented here yet**.

This folder is independent of the Sandbox web app; nothing in the app depends on it.

## What's in the image

| Component | Source | Pin |
|---|---|---|
| Base | `ubuntu:24.04`, `linux/arm64` | tag (digest: REQUIRED in `workstation.lock.yaml`) |
| CompCert | `AbsInt/CompCert` tag `v3.18`, configured `aarch64-linux` | commit `14d6160…` enforced at build |
| Coq / OCaml | opam | Coq 8.20.1, OCaml 4.14.2 |
| GNU Modula-2 | Ubuntu noble `gm2` | exact version recorded by G0 |
| Lean 4 / Lake | elan, no default toolchain | each project's `lean-toolchain` |

CompCert is distributed under a non-commercial license by INRIA/AbsInt. Check that your use
is permitted before building or publishing the image.

## Windows workstation (Docker Desktop)

Data lives on **D:** by default (`D:\lean-m2\{work,results,elan-toolchains}`).

```powershell
cd Sandbox\lean-m2\workstation
.\lean-m2.ps1 setup                  # pull the CI-built image (or: setup -Build)
.\lean-m2.ps1 info                   # shows native vs emulated
.\lean-m2.ps1 probe                  # G0, toolchain only
# copy your Lean project to D:\lean-m2\work\<name>, then:
.\lean-m2.ps1 probe -Project <name>  # full G0 incl. lean-toolchain, lake-manifest, corpus
.\lean-m2.ps1 shell                  # bash in the container, D:\lean-m2\work at /work
```

Docker Desktop keeps its own disk image on C: unless you move it in Docker Desktop's
disk image location setting. Do that if C: space matters.

### Native vs emulated

- **ARM64 Windows** (e.g. Snapdragon): the container runs natively. G0 can PASS.
- **x64 Windows**: `linux/arm64` runs under QEMU. The objects are genuine AArch64 ELF, but every
  test executed there trusts QEMU. G0 **BLOCKS** on emulation unless you run
  `probe -AllowEmulation`, which records that QEMU is part of the trusted base.
  Building the image under emulation takes hours; prefer `setup` (pull) over `setup -Build`.

Linux/macOS: `workstation/lean-m2.sh` has the same commands (`LEAN_M2_DATA` sets the data root).
VS Code: `.devcontainer/lean-m2/` opens the same image.

## G0 output

`results/g0-<timestamp>/g0-result.json` plus raw logs. Every check is `PASS`, `BLOCKED` or
`NOT_EVALUATED`. Overall status:

- `PASS`: all checks passed, project given.
- `TOOLCHAIN_ONLY_PASS`: toolchain passed; corpus deliberately not evaluated.
- `BLOCKED`: anything else (exit code 1).

G0 checks:

- host is aarch64 Linux, and the execution mode is declared;
- `lean`, `lake`, `ccomp`, `gm2`, `sha256sum` and `readelf` are present;
- CompCert version token is exactly `3.18`, and `compcert.ini` says `arch=aarch64` and `system=linux` (its hash is recorded);
- `gm2 -dumpmachine` is `aarch64-*-linux*`;
- both fixture objects are AArch64 ELF (via `readelf`);
- a **linked runtime ABI probe** (`fixtures/abi/AbiLinkProbe.mod`) passes. It covers:
  - Modula-2 → C calls,
  - C → Modula-2 through a function pointer,
  - 64-bit boundary values,
  - caller-owned buffers,
  - NULL error return,
  - and a runtime check of the type widths;
- the project has `lean-toolchain`, `lake-manifest.json` and at least one `.lean` file.

A G0 pass certifies the toolchain only. It says nothing about extraction correctness or Lean proofs.

## Files

- `toolchain.lock.yaml`: the frozen contract lockfile (schema 1.0.0, unchanged; `REQUIRED` = blocker).
- `workstation.lock.yaml`: image pins, kept separate so the frozen schema is not modified.
- `docker/Dockerfile`: the image.
- `scripts/probe-toolchain.sh`: the G0 probe.
- `fixtures/abi/`: the ABI fixtures (C compiled only by `ccomp`; Modula-2 by `gm2 -fiso`).
- `workstation/`: the launchers.
- CI: `.github/workflows/lean-m2-workstation.yml` builds on a native `ubuntu-24.04-arm` runner, runs G0, and uploads the evidence. It publishes `ghcr.io/snapkittyagent9nova/lean-m2-workstation` from `main` only.
