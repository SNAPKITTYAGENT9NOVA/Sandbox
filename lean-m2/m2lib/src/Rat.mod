(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Rat;

IMPORT BigNat, BigInt;

PROCEDURE Normalize (VAR a: T);
(* divide numerator and denominator by their gcd; zero becomes 0/1 *)
VAR
  g: BigNat.T; one: BigNat.T;
BEGIN
  BigNat.FromNat(one, 1);
  IF BigInt.IsZero(a.num) THEN a.den := one; RETURN END;
  BigNat.Gcd(a.num.mag, a.den, g);
  IF NOT BigNat.Equal(g, one) THEN
    BigNat.Div(a.num.mag, g, a.num.mag);
    BigNat.Div(a.den, g, a.den)
  END
END Normalize;

PROCEDURE FromInt (VAR r: T; x: LONGINT);
BEGIN
  BigInt.FromInt(r.num, x); BigNat.FromNat(r.den, 1)
END FromInt;

PROCEDURE FromNat (VAR r: T; x: LONGCARD);
BEGIN
  BigInt.FromNat(r.num, x); BigNat.FromNat(r.den, 1)
END FromNat;

PROCEDURE OfBigInt (VAR a: BigInt.T; VAR r: T);
BEGIN
  r.num := a; BigNat.FromNat(r.den, 1)
END OfBigInt;

PROCEDURE Make (VAR n: BigInt.T; VAR d: BigNat.T; VAR r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  IF BigNat.IsZero(d) THEN FromNat(r, 0); RETURN TRUE END;
  t.num := n; t.den := d; Normalize(t); r := t; RETURN TRUE
END Make;

PROCEDURE MakeSmall (n: LONGINT; d: LONGCARD; VAR r: T) : BOOLEAN;
VAR
  bn: BigInt.T; bd: BigNat.T;
BEGIN
  BigInt.FromInt(bn, n); BigNat.FromNat(bd, d);
  RETURN Make(bn, bd, r)
END MakeSmall;

PROCEDURE Num (VAR a: T; VAR r: BigInt.T);
BEGIN
  r := a.num
END Num;

PROCEDURE Den (VAR a: T; VAR r: BigNat.T);
BEGIN
  r := a.den
END Den;

PROCEDURE IsZero (VAR a: T) : BOOLEAN;
BEGIN
  RETURN BigInt.IsZero(a.num)
END IsZero;

PROCEDURE IsInt (VAR a: T) : BOOLEAN;
VAR
  one: BigNat.T;
BEGIN
  BigNat.FromNat(one, 1);
  RETURN BigNat.Equal(a.den, one)
END IsInt;

PROCEDURE Sign (VAR a: T) : INTEGER;
BEGIN
  RETURN BigInt.Sign(a.num)
END Sign;

PROCEDURE Cmp (VAR a, b: T; VAR c: INTEGER) : BOOLEAN;
VAR
  x, y, bd, ad: BigInt.T; sa, sb: INTEGER;
BEGIN
  sa := Sign(a); sb := Sign(b);
  IF sa # sb THEN
    IF sa < sb THEN c := -1 ELSE c := 1 END;
    RETURN TRUE
  END;
  BigInt.OfBigNat(b.den, bd); BigInt.OfBigNat(a.den, ad);
  IF NOT BigInt.Mul(a.num, bd, x) THEN RETURN FALSE END;
  IF NOT BigInt.Mul(b.num, ad, y) THEN RETURN FALSE END;
  c := BigInt.Cmp(x, y); RETURN TRUE
END Cmp;

PROCEDURE Equal (VAR a, b: T) : BOOLEAN;
BEGIN
  (* both are in lowest terms with positive denominators *)
  RETURN BigInt.Equal(a.num, b.num) AND BigNat.Equal(a.den, b.den)
END Equal;

PROCEDURE Neg (VAR a, r: T);
BEGIN
  r := a; BigInt.Neg(a.num, r.num)
END Neg;

PROCEDURE Abs (VAR a, r: T);
BEGIN
  r := a; BigInt.Abs(a.num, r.num)
END Abs;

PROCEDURE Inv (VAR a, r: T);
VAR
  t: T;
BEGIN
  IF BigInt.IsZero(a.num) THEN FromNat(r, 0); RETURN END;
  BigInt.OfBigNat(a.den, t.num);
  t.num.neg := a.num.neg;
  t.den := a.num.mag;
  r := t
END Inv;

PROCEDURE Add (VAR a, b, r: T) : BOOLEAN;
VAR
  x, y, bd, ad: BigInt.T; t: T;
BEGIN
  BigInt.OfBigNat(b.den, bd); BigInt.OfBigNat(a.den, ad);
  IF NOT BigInt.Mul(a.num, bd, x) THEN RETURN FALSE END;
  IF NOT BigInt.Mul(b.num, ad, y) THEN RETURN FALSE END;
  IF NOT BigInt.Add(x, y, t.num) THEN RETURN FALSE END;
  IF NOT BigNat.Mul(a.den, b.den, t.den) THEN RETURN FALSE END;
  Normalize(t); r := t; RETURN TRUE
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
  IF NOT BigInt.Mul(a.num, b.num, t.num) THEN RETURN FALSE END;
  IF NOT BigNat.Mul(a.den, b.den, t.den) THEN RETURN FALSE END;
  Normalize(t); r := t; RETURN TRUE
END Mul;

PROCEDURE Div (VAR a, b, r: T) : BOOLEAN;
VAR
  ib: T;
BEGIN
  Inv(b, ib);
  RETURN Mul(a, ib, r)
END Div;

PROCEDURE Pow (VAR a: T; e: LONGCARD; VAR r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  IF NOT BigInt.Pow(a.num, e, t.num) THEN RETURN FALSE END;
  IF NOT BigNat.Pow(a.den, e, t.den) THEN RETURN FALSE END;
  r := t; RETURN TRUE                        (* powers of coprime parts stay coprime *)
END Pow;

PROCEDURE ZPow (VAR a: T; e: LONGINT; VAR r: T) : BOOLEAN;
VAR
  t: T; k: LONGCARD;
BEGIN
  IF e >= 0 THEN RETURN Pow(a, VAL(LONGCARD, e), r) END;
  k := VAL(LONGCARD, -(e + 1)) + 1;
  IF NOT Pow(a, k, t) THEN RETURN FALSE END;
  Inv(t, r); RETURN TRUE
END ZPow;

PROCEDURE Floor (VAR a: T; VAR r: BigInt.T) : BOOLEAN;
VAR
  d: BigInt.T;
BEGIN
  BigInt.OfBigNat(a.den, d);
  RETURN BigInt.Div(a.num, d, r)             (* Euclidean division by a positive divisor is floor *)
END Floor;

PROCEDURE Ceil (VAR a: T; VAR r: BigInt.T) : BOOLEAN;
VAR
  na: T; f: BigInt.T;
BEGIN
  Neg(a, na);
  IF NOT Floor(na, f) THEN RETURN FALSE END;
  BigInt.Neg(f, r); RETURN TRUE
END Ceil;

PROCEDURE NatFloor (VAR a: T; VAR r: BigNat.T);
VAR
  f: BigInt.T;
BEGIN
  IF a.num.neg OR NOT Floor(a, f) THEN r.n := 0; RETURN END;
  BigInt.ToNat(f, r)
END NatFloor;

PROCEDURE ToText (VAR a: T; VAR s: ARRAY OF CHAR) : BOOLEAN;
VAR
  ns, ds: ARRAY [0..2600] OF CHAR; i, j: CARDINAL;
BEGIN
  IF NOT BigInt.ToDecimal(a.num, ns) THEN RETURN FALSE END;
  i := 0;
  WHILE ns[i] # 0C DO
    IF i > HIGH(s) THEN RETURN FALSE END;
    s[i] := ns[i]; INC(i)
  END;
  IF NOT IsInt(a) THEN
    IF NOT BigNat.ToDecimal(a.den, ds) THEN RETURN FALSE END;
    IF i > HIGH(s) THEN RETURN FALSE END;
    s[i] := '/'; INC(i);
    j := 0;
    WHILE ds[j] # 0C DO
      IF i > HIGH(s) THEN RETURN FALSE END;
      s[i] := ds[j]; INC(i); INC(j)
    END
  END;
  IF i > HIGH(s) THEN RETURN FALSE END;
  s[i] := 0C; RETURN TRUE
END ToText;

END Rat.
