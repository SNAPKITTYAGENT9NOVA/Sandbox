# syntax=docker/dockerfile:1
# check=skip=FromPlatformFlagConstDisallowed
# SPDX-License-Identifier: AGPL-3.0-only
# Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project)
# (linux/arm64 is the contract target, so the constant platform is intentional.)
# LEAN-M2-CC-001 workstation image: AArch64 Linux with Lean 4 (elan), GNU Modula-2, CompCert 3.18.
#
# Target is ALWAYS linux/arm64. On an x86-64 workstation this runs under QEMU emulation;
# the G0 probe records that and blocks unless emulation is explicitly allowed.
#
# Pins:
#   - CompCert source: commit 8135de0, the direct child of tag v3.18 (14d6160). The tagged commit's
#     VERSION file still says 3.17, so its ccomp reports itself as 3.17. Upstream fixed that in
#     8135de0 ("Update CompCert version to match latest release"), which changes ONLY `VERSION`.
#     The build re-verifies that the tag-to-pin diff touches nothing else.
#   - Coq 8.20.1 is inside CompCert 3.18's documented range (Coq 8.15.0-8.20.1 / Rocq 9.0-9.2).
#   - Base image is pinned by tag only; pin by digest in workstation.lock.yaml after first pull.
#   - gm2 comes from Ubuntu noble's archive; the exact version is recorded by the probe, not assumed.

FROM --platform=linux/arm64 ubuntu:24.04

ARG COMPCERT_TAG=v3.18
ARG COMPCERT_TAG_COMMIT=14d616046360a0b2611ebdfc2f98368af402e1f7
ARG COMPCERT_COMMIT=8135de0cc006f094e4a96aff9bb76cf716c9065a
ARG OCAML_VERSION=4.14.2
ARG COQ_VERSION=8.20.1

ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git xz-utils unzip \
        build-essential binutils m4 pkg-config libgmp-dev \
        gm2 \
        opam \
        python3 \
    && rm -rf /var/lib/apt/lists/*

RUN useradd --create-home --shell /bin/bash builder \
    && mkdir -p /opt/compcert /opt/lean-m2 /work \
    && chown builder:builder /opt/compcert /opt/lean-m2 /work

USER builder
WORKDIR /home/builder

# --- OCaml + Coq + Menhir (CompCert build prerequisites) ---
RUN opam init --bare --disable-sandboxing -y \
    && opam switch create default "${OCAML_VERSION}" -y \
    && opam install -y "coq.${COQ_VERSION}" menhir \
    && opam clean -a -c -s --logs

# --- CompCert, built from a commit-verified checkout, configured for aarch64-linux ---
RUN git init -q /tmp/compcert && cd /tmp/compcert \
    && git fetch -q --depth 2 https://github.com/AbsInt/CompCert.git "${COMPCERT_COMMIT}" \
    && git fetch -q --depth 1 https://github.com/AbsInt/CompCert.git "refs/tags/${COMPCERT_TAG}:refs/tags/${COMPCERT_TAG}" \
    && git checkout -q "${COMPCERT_COMMIT}" \
    && test "$(git rev-parse HEAD)" = "${COMPCERT_COMMIT}" \
    && test "$(git rev-parse "${COMPCERT_TAG}^{commit}")" = "${COMPCERT_TAG_COMMIT}" \
    && test "$(git diff --name-only "${COMPCERT_TAG}" HEAD)" = "VERSION" \
         || { echo "BLOCKED: CompCert pin is not ${COMPCERT_TAG} + VERSION-only change"; exit 1; } \
    && grep -qx 'version=3.18' VERSION \
    && eval "$(opam env --switch=default)" \
    && ./configure -prefix /opt/compcert aarch64-linux \
    && make -j"$(nproc)" all \
    && make install \
    && printf 'tag=%s\ntag_commit=%s\ncommit=%s\nnote=tag + upstream VERSION-only fix\nconfigure=-prefix /opt/compcert aarch64-linux\n' \
         "${COMPCERT_TAG}" "${COMPCERT_TAG_COMMIT}" "${COMPCERT_COMMIT}" > /opt/lean-m2/compcert-source.txt \
    && rm -rf /tmp/compcert

# --- Lean 4 via elan. No default toolchain: each project's lean-toolchain file decides. ---
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none

ENV PATH="/opt/compcert/bin:/home/builder/.elan/bin:${PATH}"

COPY --chown=builder:builder scripts/  /opt/lean-m2/scripts/
COPY --chown=builder:builder fixtures/ /opt/lean-m2/fixtures/

WORKDIR /work
CMD ["/bin/bash"]
