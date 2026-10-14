#!/usr/bin/env bash
# LEAN-M2-CC-001 workstation launcher for Linux / macOS hosts (Docker).
# Mirrors lean-m2.ps1:  setup [--build] | probe [project] | shell | info
# Data root: $LEAN_M2_DATA (default ~/lean-m2). Emulated hosts need LEAN_M2_ALLOW_EMULATION=1.
set -euo pipefail

IMAGE="${LEAN_M2_IMAGE:-ghcr.io/snapkittyagent9nova/lean-m2-workstation:main}"
DATA="${LEAN_M2_DATA:-$HOME/lean-m2}"
HERE="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$DATA/work" "$DATA/elan-toolchains" "$DATA/results"

case "$(uname -m)" in aarch64|arm64) EXECUTION=native ;; *) EXECUTION=emulated ;; esac

container() {
  docker run --rm --platform linux/arm64 "$@"
}
mounts=(-e "LEAN_M2_EXECUTION=$EXECUTION" -e "LEAN_M2_ALLOW_EMULATION=${LEAN_M2_ALLOW_EMULATION:-0}"
        -v "$DATA/work:/work" -v "$DATA/elan-toolchains:/home/builder/.elan/toolchains" -v "$DATA/results:/results")

case "${1:-}" in
  info)  echo "host=$(uname -m) execution=$EXECUTION data=$DATA image=$IMAGE" ;;
  setup) if [ "${2:-}" = --build ]; then
           docker build --platform linux/arm64 -t "$IMAGE" -f "$HERE/docker/Dockerfile" "$HERE"
         else docker pull --platform linux/arm64 "$IMAGE"; fi
         docker image inspect "$IMAGE" --format '{{json .RepoDigests}} {{.Id}}' > "$DATA/results/image-identity.txt" ;;
  probe) stamp="$(date -u +%Y%m%dT%H%M%SZ)"
         target="${2:+/work/$2}"; target="${target:---toolchain-only}"
         container "${mounts[@]}" "$IMAGE" bash -c "OUT=/results/g0-$stamp /opt/lean-m2/scripts/probe-toolchain.sh $target"
         ;;
  shell) container -it "${mounts[@]}" "$IMAGE" bash ;;
  *)     echo "usage: $0 setup [--build] | probe [project] | shell | info" >&2; exit 2 ;;
esac
