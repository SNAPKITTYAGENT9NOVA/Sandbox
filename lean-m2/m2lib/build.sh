#!/bin/sh
# Build the library with GNU Modula-2 (ISO dialect), link and run every test program.
# Exits non-zero if any module fails to compile, any test program fails to link,
# any test fails, or the expected-failure program does not fail.
#   GM2      compiler (default: gm2 on PATH)
#   GM2LIB   directory holding libm2iso.so etc., recorded as the run-time path (optional)
set -u
cd "$(dirname "$0")"
GM2=${GM2:-gm2}
FLAGS="-fiso -g -O1 -Isrc -Itests"
LINK=""
if [ -n "${GM2LIB:-}" ]; then LINK="-Wl,-rpath,$GM2LIB"; fi
MODULES="NatArith NumberTheory BigNat BigInt Rat Combinatorics Digits NatSeq ModArith Matrix Poly NatSearch OeisNat OeisInt"
TESTS="TestCore TestBig TestSeq TestSearch TestOeis"
mkdir -p build
status=0

run() {                      # run a command, print it with its exit code
  "$@"
  rc=$?
  echo "[exit $rc] $*"
  return $rc
}

for m in $MODULES; do
  run $GM2 $FLAGS -c "src/$m.mod" -o "build/$m.o" || status=1
done
run $GM2 $FLAGS -c tests/Check.mod -o build/Check.o || status=1
if [ $status -ne 0 ]; then echo "BUILD FAILED"; exit 1; fi

OBJS=""
for m in $MODULES Check; do OBJS="$OBJS build/$m.o"; done
for t in $TESTS; do
  run $GM2 $FLAGS "tests/$t.mod" $OBJS $LINK -o "build/$t" || { status=1; continue; }
  run "./build/$t" || status=1
done

# a test program with deliberately wrong expectations must fail
if run $GM2 $FLAGS tests/expect_fail/FailCheck.mod $OBJS $LINK -o build/FailCheck; then
  if ./build/FailCheck; then
    echo "[exit 0] ./build/FailCheck  -- ERROR: expected a non-zero exit status"; status=1
  else
    echo "[exit $?] ./build/FailCheck  -- failed as required"
  fi
else
  status=1
fi

if [ $status -ne 0 ]; then echo "RESULT: FAILED"; else echo "RESULT: ALL PASSED"; fi
exit $status
