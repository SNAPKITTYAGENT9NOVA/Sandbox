(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE AbiLinkProbe;
(* Linked + runtime ABI probe: Modula-2 (gm2) <-> C (ccomp), both directions.
   Exit status 0 only if every check passes. *)
FROM SYSTEM IMPORT ADR, TSIZE, ADDRESS;
FROM libc IMPORT printf, exit;
FROM abi_probe_c IMPORT cc_add64, cc_sum_buf, cc_apply;
FROM AbiProbe IMPORT M2Add64;

VAR
  fails: INTEGER;
  buf:   ARRAY [0..3] OF LONGINT;
  out:   LONGINT;
  rc:    INTEGER;

PROCEDURE Ok (cond: BOOLEAN);
BEGIN
  IF cond THEN printf("PASS\n") ELSE printf("FAIL\n"); INC(fails) END
END Ok;

BEGIN
  fails := 0;
  printf("width LONGINT=8: ");  Ok(TSIZE(LONGINT) = 8);
  printf("width LONGCARD=8: "); Ok(TSIZE(LONGCARD) = 8);
  printf("width INTEGER=4: ");  Ok(TSIZE(INTEGER) = 4);
  printf("width ADDRESS=8: ");  Ok(TSIZE(ADDRESS) = 8);

  printf("m2->c add64: ");          Ok(cc_add64(-5, 7) = 2);
  printf("m2->c add64 at MIN: ");   Ok(cc_add64(MIN(LONGINT) + 1, -1) = MIN(LONGINT));
  printf("m2->c add64 at MAX: ");   Ok(cc_add64(MAX(LONGINT) - 1, 1) = MAX(LONGINT));

  buf[0] := 1; buf[1] := 2; buf[2] := 3; buf[3] := MAX(LONGINT) - 6;
  out := 0;
  rc := cc_sum_buf(ADR(buf), 4, ADR(out));
  printf("m2->c buffer rc: ");      Ok(rc = 0);
  printf("m2->c buffer sum: ");     Ok(out = MAX(LONGINT));
  rc := cc_sum_buf(NIL, 4, ADR(out));
  printf("m2->c NULL error: ");     Ok(rc = -1);
  rc := cc_sum_buf(ADR(buf), 0, ADR(out));
  printf("m2->c empty buffer: ");   Ok((rc = 0) AND (out = 0));

  printf("c->m2 callback: ");       Ok(cc_apply(M2Add64, 40, 2) = 42);
  printf("c->m2 callback neg: ");   Ok(cc_apply(M2Add64, MIN(LONGINT) + 1, -1) = MIN(LONGINT));

  IF fails = 0 THEN printf("ABI LINK PROBE: PASS\n"); exit(0)
  ELSE printf("ABI LINK PROBE: FAIL\n"); exit(1) END
END AbiLinkProbe.
