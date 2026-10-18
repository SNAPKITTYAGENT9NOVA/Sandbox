(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE CunninghamChain;
(* Same algorithm and guards as lm2_cunningham.c; justified by Spec.lean:
     overflow_of_ge_65 (short-circuit) and the per-step guard t <= (MAX - 1) DIV 2. *)

CONST
  MaxHalf = (MAX(LONGCARD) - 1) DIV 2;

PROCEDURE FirstKindTerm (p, n: LONGCARD; VAR out: LONGCARD) : INTEGER;
VAR
  t, i: LONGCARD;
BEGIN
  IF n >= 65 THEN
    RETURN Overflow
  END;
  t := p;
  i := 0;
  WHILE i < n DO
    IF t > MaxHalf THEN
      RETURN Overflow
    END;
    t := 2 * t + 1;
    INC(i)
  END;
  out := t;
  RETURN Ok
END FirstKindTerm;

END CunninghamChain.
