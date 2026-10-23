(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE BigInt;

IMPORT BigNat;

PROCEDURE Fix (VAR a: T);
BEGIN
  IF BigNat.IsZero(a.mag) THEN a.neg := FALSE END
END Fix;

PROCEDURE FromNat (VAR r: T; x: LONGCARD);
BEGIN
  r.neg := FALSE; BigNat.FromNat(r.mag, x)
END FromNat;

PROCEDURE FromInt (VAR r: T; x: LONGINT);
BEGIN
  IF x >= 0 THEN
    r.neg := FALSE; BigNat.FromNat(r.mag, VAL(LONGCARD, x))
  ELSE
    (* |x| = -(x + 1) + 1 avoids negating MIN(LONGINT) *)
    r.neg := TRUE; BigNat.FromNat(r.mag, VAL(LONGCARD, -(x + 1)) + 1)
  END
END FromInt;

PROCEDURE OfBigNat (VAR a: BigNat.T; VAR r: T);
BEGIN
  r.mag := a; r.neg := FALSE
END OfBigNat;

PROCEDURE ToInt (VAR a: T; VAR x: LONGINT) : BOOLEAN;
VAR
  m, lim: LONGCARD;
BEGIN
  IF NOT BigNat.ToNat(a.mag, m) THEN RETURN FALSE END;
  lim := VAL(LONGCARD, MAX(LONGINT));
  IF NOT a.neg THEN
    IF m > lim THEN RETURN FALSE END;
    x := VAL(LONGINT, m); RETURN TRUE
  END;
  IF m > lim + 1 THEN RETURN FALSE END;
  IF m = lim + 1 THEN x := MIN(LONGINT) ELSE x := -VAL(LONGINT, m) END;
  RETURN TRUE
END ToInt;

PROCEDURE ToNat (VAR a: T; VAR r: BigNat.T);
BEGIN
  IF a.neg THEN r.n := 0 ELSE r := a.mag END
END ToNat;

PROCEDURE NatAbs (VAR a: T; VAR r: BigNat.T);
BEGIN
  r := a.mag
END NatAbs;

PROCEDURE IsZero (VAR a: T) : BOOLEAN;
BEGIN
  RETURN BigNat.IsZero(a.mag)
END IsZero;

PROCEDURE IsNeg (VAR a: T) : BOOLEAN;
BEGIN
  RETURN a.neg
END IsNeg;

PROCEDURE Sign (VAR a: T) : INTEGER;
BEGIN
  IF BigNat.IsZero(a.mag) THEN RETURN 0 END;
  IF a.neg THEN RETURN -1 END;
  RETURN 1
END Sign;

PROCEDURE Cmp (VAR a, b: T) : INTEGER;
BEGIN
  IF a.neg # b.neg THEN
    IF a.neg THEN RETURN -1 ELSE RETURN 1 END
  END;
  IF a.neg THEN RETURN -BigNat.Cmp(a.mag, b.mag) END;
  RETURN BigNat.Cmp(a.mag, b.mag)
END Cmp;

PROCEDURE Equal (VAR a, b: T) : BOOLEAN;
BEGIN
  RETURN Cmp(a, b) = 0
END Equal;

PROCEDURE Neg (VAR a, r: T);
BEGIN
  r := a; r.neg := NOT a.neg; Fix(r)
END Neg;

PROCEDURE Abs (VAR a, r: T);
BEGIN
  r := a; r.neg := FALSE
END Abs;

PROCEDURE Add (VAR a, b, r: T) : BOOLEAN;
VAR
  t: T; c: INTEGER;
BEGIN
  IF a.neg = b.neg THEN
    IF NOT BigNat.Add(a.mag, b.mag, t.mag) THEN RETURN FALSE END;
    t.neg := a.neg
  ELSE
    c := BigNat.Cmp(a.mag, b.mag);
    IF c >= 0 THEN BigNat.Sub(a.mag, b.mag, t.mag); t.neg := a.neg
    ELSE BigNat.Sub(b.mag, a.mag, t.mag); t.neg := b.neg END
  END;
  Fix(t); r := t; RETURN TRUE
END Add;

PROCEDURE Sub (VAR a, b, r: T) : BOOLEAN;
VAR
  nb: T;
BEGIN
  Neg(b, nb);
  RETURN Add(a, nb, r)
END Sub;

PROCEDURE Mul (VAR a, b, r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  IF NOT BigNat.Mul(a.mag, b.mag, t.mag) THEN RETURN FALSE END;
  t.neg := a.neg # b.neg; Fix(t); r := t; RETURN TRUE
END Mul;

PROCEDURE DivMod (VAR a, b, q, m: T) : BOOLEAN;
(* Euclidean: with q0 = |a| / |b| and r0 = |a| % |b|,
   a >= 0: q = sign(b) * q0, m = r0;
   a < 0, r0 = 0: q = -sign(b) * q0, m = 0;
   a < 0, r0 > 0: q = -sign(b) * (q0 + 1), m = |b| - r0. *)
VAR
  q0, r0: BigNat.T; tq, tm: T;
BEGIN
  IF BigNat.IsZero(b.mag) THEN
    tm := a; FromNat(q, 0); m := tm; RETURN TRUE
  END;
  BigNat.DivMod(a.mag, b.mag, q0, r0);
  IF a.neg AND NOT BigNat.IsZero(r0) THEN
    IF NOT BigNat.AddSmall(q0, 1, q0) THEN RETURN FALSE END;
    BigNat.Sub(b.mag, r0, r0)
  END;
  tq.mag := q0; tq.neg := a.neg # b.neg; Fix(tq);
  tm.mag := r0; tm.neg := FALSE;
  q := tq; m := tm; RETURN TRUE
END DivMod;

PROCEDURE Div (VAR a, b, r: T) : BOOLEAN;
VAR
  q, m: T;
BEGIN
  IF NOT DivMod(a, b, q, m) THEN RETURN FALSE END;
  r := q; RETURN TRUE
END Div;

PROCEDURE Mod (VAR a, b, r: T) : BOOLEAN;
VAR
  q, m: T;
BEGIN
  IF NOT DivMod(a, b, q, m) THEN RETURN FALSE END;
  r := m; RETURN TRUE
END Mod;

PROCEDURE Pow (VAR a: T; e: LONGCARD; VAR r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  IF NOT BigNat.Pow(a.mag, e, t.mag) THEN RETURN FALSE END;
  t.neg := a.neg AND ODD(e); Fix(t); r := t; RETURN TRUE
END Pow;

PROCEDURE Gcd (VAR a, b: T; VAR r: BigNat.T);
BEGIN
  BigNat.Gcd(a.mag, b.mag, r)
END Gcd;

PROCEDURE ToDecimal (VAR a: T; VAR s: ARRAY OF CHAR) : BOOLEAN;
VAR
  buf: ARRAY [0..2600] OF CHAR; i, n: CARDINAL;
BEGIN
  IF NOT BigNat.ToDecimal(a.mag, buf) THEN RETURN FALSE END;
  n := 0; WHILE buf[n] # 0C DO INC(n) END;
  IF a.neg THEN
    IF n + 1 > HIGH(s) THEN RETURN FALSE END;
    s[0] := '-';
    i := 0; WHILE i < n DO s[i + 1] := buf[i]; INC(i) END;
    s[n + 1] := 0C
  ELSE
    IF n > HIGH(s) THEN RETURN FALSE END;
    i := 0; WHILE i < n DO s[i] := buf[i]; INC(i) END;
    s[n] := 0C
  END;
  RETURN TRUE
END ToDecimal;

PROCEDURE FromDecimal (s: ARRAY OF CHAR; VAR r: T) : BOOLEAN;
VAR
  body: ARRAY [0..2600] OF CHAR; i, j: CARDINAL; t: T;
BEGIN
  i := 0; t.neg := FALSE;
  IF s[0] = '-' THEN t.neg := TRUE; i := 1 END;
  j := 0;
  WHILE (i <= HIGH(s)) AND (s[i] # 0C) AND (j < HIGH(body)) DO body[j] := s[i]; INC(i); INC(j) END;
  body[j] := 0C;
  IF NOT BigNat.FromDecimal(body, t.mag) THEN RETURN FALSE END;
  Fix(t); r := t; RETURN TRUE
END FromDecimal;

END BigInt.
