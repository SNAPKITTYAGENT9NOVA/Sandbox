(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Check;

IMPORT STextIO, Rat, FIO;

VAR
  passed, failed: CARDINAL;

PROCEDURE PutNat (x: LONGCARD);
VAR buf: ARRAY [0..24] OF CHAR; i: CARDINAL;
BEGIN
  i := 0;
  REPEAT buf[i] := CHR(ORD('0') + VAL(CARDINAL, x MOD 10)); x := x DIV 10; INC(i) UNTIL x = 0;
  WHILE i > 0 DO DEC(i); STextIO.WriteChar(buf[i]) END
END PutNat;

PROCEDURE PutInt (x: LONGINT);
BEGIN
  IF x < 0 THEN STextIO.WriteChar('-'); PutNat(VAL(LONGCARD, -(x + 1)) + 1)
  ELSE PutNat(VAL(LONGCARD, x)) END
END PutInt;

PROCEDURE Head (name: ARRAY OF CHAR; arg: LONGCARD);
BEGIN
  STextIO.WriteString("FAIL "); STextIO.WriteString(name);
  STextIO.WriteChar('('); PutNat(arg); STextIO.WriteString("): ")
END Head;

PROCEDURE Pass;
BEGIN
  INC(passed)
END Pass;

PROCEDURE Fail;
BEGIN
  INC(failed); STextIO.WriteLn
END Fail;

PROCEDURE Nat (name: ARRAY OF CHAR; arg: LONGCARD; ok: BOOLEAN; got, want: LONGCARD);
BEGIN
  IF ok AND (got = want) THEN Pass; RETURN END;
  Head(name, arg);
  IF NOT ok THEN STextIO.WriteString("returned FALSE") ELSE PutNat(got) END;
  STextIO.WriteString(", expected "); PutNat(want); Fail
END Nat;

PROCEDURE Int (name: ARRAY OF CHAR; arg: LONGCARD; ok: BOOLEAN; got, want: LONGINT);
BEGIN
  IF ok AND (got = want) THEN Pass; RETURN END;
  Head(name, arg);
  IF NOT ok THEN STextIO.WriteString("returned FALSE") ELSE PutInt(got) END;
  STextIO.WriteString(", expected "); PutInt(want); Fail
END Int;

PROCEDURE RatFrac (name: ARRAY OF CHAR; arg: LONGCARD; ok: BOOLEAN; VAR got: Rat.T;
                   num: LONGINT; den: LONGCARD);
VAR w: Rat.T; s: ARRAY [0..2600] OF CHAR;
BEGIN
  IF ok AND Rat.MakeSmall(num, den, w) AND Rat.Equal(got, w) THEN Pass; RETURN END;
  Head(name, arg);
  IF NOT ok THEN STextIO.WriteString("returned FALSE")
  ELSIF Rat.ToText(got, s) THEN STextIO.WriteString(s)
  ELSE STextIO.WriteString("<unprintable>") END;
  STextIO.WriteString(", expected "); PutInt(num); STextIO.WriteChar('/'); PutNat(den); Fail
END RatFrac;

PROCEDURE RatInt (name: ARRAY OF CHAR; arg: LONGCARD; ok: BOOLEAN; VAR got: Rat.T; want: LONGINT);
BEGIN
  RatFrac(name, arg, ok, got, want, 1)
END RatInt;

PROCEDURE Equal (VAR a, b: ARRAY OF CHAR) : BOOLEAN;
VAR i: CARDINAL; ca, cb: CHAR;
BEGIN
  i := 0;
  LOOP
    IF i <= HIGH(a) THEN ca := a[i] ELSE ca := 0C END;
    IF i <= HIGH(b) THEN cb := b[i] ELSE cb := 0C END;
    IF ca # cb THEN RETURN FALSE END;
    IF ca = 0C THEN RETURN TRUE END;
    INC(i)
  END
END Equal;

PROCEDURE Text (name: ARRAY OF CHAR; ok: BOOLEAN; got, want: ARRAY OF CHAR);
BEGIN
  IF ok AND Equal(got, want) THEN Pass; RETURN END;
  STextIO.WriteString("FAIL "); STextIO.WriteString(name); STextIO.WriteString(": ");
  IF NOT ok THEN STextIO.WriteString("returned FALSE") ELSE STextIO.WriteString(got) END;
  STextIO.WriteString(", expected "); STextIO.WriteString(want); Fail
END Text;

PROCEDURE True (name: ARRAY OF CHAR; cond: BOOLEAN);
BEGIN
  IF cond THEN Pass; RETURN END;
  STextIO.WriteString("FAIL "); STextIO.WriteString(name); Fail
END True;

PROCEDURE Fails (name: ARRAY OF CHAR; arg: LONGCARD; ok: BOOLEAN);
BEGIN
  IF NOT ok THEN Pass; RETURN END;
  Head(name, arg); STextIO.WriteString("returned TRUE, expected FALSE (capacity/bound)"); Fail
END Fails;

PROCEDURE Done (suite: ARRAY OF CHAR);
BEGIN
  STextIO.WriteString(suite); STextIO.WriteString(": ");
  PutNat(VAL(LONGCARD, passed)); STextIO.WriteString(" passed, ");
  PutNat(VAL(LONGCARD, failed)); STextIO.WriteString(" failed"); STextIO.WriteLn;
  FIO.FlushBuffer(FIO.StdOut);                    (* HALT does not flush the last line *)
  IF failed > 0 THEN HALT(1) END
END Done;

BEGIN
  passed := 0; failed := 0
END Check.
