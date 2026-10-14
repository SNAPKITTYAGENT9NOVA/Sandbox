# syntax=docker/dockerfile:1
# LEAN-M2-CC-001 workstation image: AArch64 Linux with Lean 4 (elan), GNU Modula-2, CompCert 3.18.
#
# Target is ALWAYS linux/arm64. On an x86-64 workstation this runs under QEMU emulation;
# the G0 probe records that and blocks unless emulation is explicitly allowed.
#
# Pins:
#   - CompCert source: tag v3.18, commit verified below (observed via `git ls-remote`, 2026-10-14).
#   - Coq 8.20.1 is inside CompCert 3.18's documented range (Coq 8.15.0-8.20.1 / Rocq 9.0-9.2).
#   - Base image is pinned by tag only; pin by digest in workstation.lock.yaml after first pull.
#   - gm2 comes from Ubuntu noble's archive; the exact version is recorded by the probe, not assumed.

FROM --platform=linux/arm64 ubuntu:24.04

ARG COMPCERT_TAG=v3.18
ARG COMPCERT_COMMIT=14d616046360a0b2611ebdfc2f98368af402e1f7
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
RUN git clone --depth 1 --branch "${COMPCERT_TAG}" https://github.com/AbsInt/CompCert.git /tmp/compcert \
    && cd /tmp/compcert \
    && test "$(git rev-parse HEAD)" = "${COMPCERT_COMMIT}" \
         || { echo "BLOCKED: CompCert ${COMPCERT_TAG} is not commit ${COMPCERT_COMMIT}"; exit 1; } \
    && eval "$(opam env --switch=default)" \
    && ./configure -prefix /opt/compcert aarch64-linux \
    && make -j"$(nproc)" all \
    && make install \
    && printf 'tag=%s\ncommit=%s\nconfigure=-prefix /opt/compcert aarch64-linux\n' \
         "${COMPCERT_TAG}" "${COMPCERT_COMMIT}" > /opt/lean-m2/compcert-source.txt \
    && rm -rf /tmp/compcert

# --- Lean 4 via elan. No default toolchain: each project's lean-toolchain file decides. ---
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none

ENV PATH="/opt/compcert/bin:/home/builder/.elan/bin:${PATH}"

COPY --chown=builder:builder scripts/  /opt/lean-m2/scripts/
COPY --chown=builder:builder fixtures/ /opt/lean-m2/fixtures/

WORKDIR /work
CMD ["/bin/bash"]
