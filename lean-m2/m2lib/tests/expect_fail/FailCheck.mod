(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE FailCheck;
(* Must exit with status 1: shows that a wrong expectation is reported as a failure, and that
   a capacity overflow is not silently accepted as a value. build.sh requires a non-zero
   exit status from this program. *)

IMPORT Check, Combinatorics, NatArith;

VAR
  n: LONGCARD; ok: BOOLEAN;

BEGIN
  ok := Combinatorics.Factorial(5, n);
  Check.Nat("deliberately wrong: 5! = 121", 5, ok, n, 121);
  ok := NatArith.Pow(2, 64, n);
  Check.Nat("deliberately wrong: 2^64 treated as a value", 64, ok, n, 0);
  Check.Done("FailCheck")
END FailCheck.
