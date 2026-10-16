MODULE GenTest;
(* LEAN-M2-CC-001 MathIR v1 differential driver (hand-written, fixed).
   For every Lean reference case it runs the generated function twice:
     C   : CompCert-compiled lm2_gen.c through the FOR "C" binding (lm2_gen_call)
     M2  : generated native Modula-2 (LM2Gen.Call)
   and classifies each result against Lean:
     PASS        Lean value fits and machine OK with the same value,
                 or Lean value does not fit and machine OVERFLOW (out untouched)
     UNSOUND     machine OK with a different value, OK although Lean's value does not fit,
                 any other status, or out written on OVERFLOW           -> must be 0
     INCOMPLETE  Lean value fits but machine OVERFLOW (an intermediate overflowed); reported
   Exit 0 iff there are no UNSOUND results. *)

FROM SYSTEM IMPORT ADR, TSIZE;
FROM libc IMPORT printf, exit;
FROM lm2_gen_bind IMPORT lm2_gen_call, lm2_gen_count;
FROM lm2_gen_cases IMPORT lm2_gen_case_count, lm2_gen_case_get;
IMPORT LM2Gen;

CONST
  Sentinel = 0DEADBEEFCAFEF00DH;
  MaxFn = 1023;   (* per-function incompleteness counters *)

VAR
  i, count, fn: CARDINAL;
  a0, a1, a2, ev, cv, mv: LONGCARD;
  est, cst, mst: INTEGER;
  refOk, refOv, unsoundC, unsoundM, incompC, incompM: CARDINAL;
  ic0, im0: CARDINAL;
  perC, perM, perCases: ARRAY [0..MaxFn] OF CARDINAL;

PROCEDURE Classify (est: INTEGER; ev: LONGCARD; st: INTEGER; v: LONGCARD;
                    VAR unsound, incomplete: CARDINAL) : BOOLEAN;
(* returns TRUE iff the result is UNSOUND *)
BEGIN
  IF est = 0 THEN
    IF st = 0 THEN
      IF v # ev THEN INC(unsound); RETURN TRUE END
    ELSIF st = 1 THEN
      IF v # Sentinel THEN INC(unsound); RETURN TRUE END;
      INC(incomplete)
    ELSE
      INC(unsound); RETURN TRUE
    END
  ELSE
    IF (st # 1) OR (v # Sentinel) THEN INC(unsound); RETURN TRUE END
  END;
  RETURN FALSE
END Classify;

BEGIN
  IF (TSIZE(LONGCARD) # 8) OR (TSIZE(CARDINAL) # 4) OR (TSIZE(INTEGER) # 4) THEN
    printf("FAIL type widths\n"); exit(2)
  END;
  count := lm2_gen_case_count();
  refOk := 0; refOv := 0; unsoundC := 0; unsoundM := 0; incompC := 0; incompM := 0;
  i := 0;
  WHILE i <= MaxFn DO perC[i] := 0; perM[i] := 0; perCases[i] := 0; INC(i) END;
  IF lm2_gen_count() > MaxFn THEN printf("FAIL more than %u functions\n", MaxFn); exit(2) END;
  i := 0;
  WHILE i < count DO
    IF lm2_gen_case_get(i, ADR(fn), ADR(a0), ADR(a1), ADR(a2), ADR(est), ADR(ev)) # 0 THEN
      printf("FAIL reading case %u\n", i); exit(2)
    END;
    IF est = 0 THEN INC(refOk) ELSE INC(refOv) END;
    cv := Sentinel; mv := Sentinel;
    ic0 := incompC; im0 := incompM;
    cst := lm2_gen_call(fn, a0, a1, a2, ADR(cv));
    mst := LM2Gen.Call(fn, a0, a1, a2, mv);
    IF Classify(est, ev, cst, cv, unsoundC, incompC) AND (unsoundC <= 20) THEN
      printf("UNSOUND C  case %u fn %u: status %d expected %d\n", i, fn, cst, est)
    END;
    IF Classify(est, ev, mst, mv, unsoundM, incompM) AND (unsoundM <= 20) THEN
      printf("UNSOUND M2 case %u fn %u: status %d expected %d\n", i, fn, mst, est)
    END;
    IF fn <= MaxFn THEN
      INC(perCases[fn]);
      IF incompC # ic0 THEN INC(perC[fn]) END;
      IF incompM # im0 THEN INC(perM[fn]) END
    END;
    INC(i)
  END;
  (* per-function incompleteness: fn index = position in the report's "translated" list *)
  i := 0;
  WHILE i <= MaxFn DO
    IF (perC[i] # 0) OR (perM[i] # 0) THEN
      printf("MATHIR INCOMPLETE fn=%u cases=%u C=%u M2=%u\n", i, perCases[i], perC[i], perM[i])
    END;
    INC(i)
  END;
  printf("MATHIR functions=%u cases=%u ref_ok=%u ref_overflow=%u\n", lm2_gen_count(), count, refOk, refOv);
  printf("MATHIR C:  unsound=%u incomplete=%u\n", unsoundC, incompC);
  printf("MATHIR M2: unsound=%u incomplete=%u\n", unsoundM, incompM);
  IF (count > 0) AND (unsoundC = 0) AND (unsoundM = 0) THEN
    printf("MATHIR DIFFERENTIAL: PASS (sound on every case)\n"); exit(0)
  ELSE
    printf("MATHIR DIFFERENTIAL: FAIL\n"); exit(1)
  END
END GenTest.
