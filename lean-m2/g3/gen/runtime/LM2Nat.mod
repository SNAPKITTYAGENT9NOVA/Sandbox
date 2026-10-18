(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE LM2Nat;

CONST
  Top = MAX(LONGCARD);

PROCEDURE Add (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF a > Top - b THEN RETURN TRUE END;
  r := a + b; RETURN FALSE
END Add;

PROCEDURE Mul (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF (a # 0) AND (b > Top DIV a) THEN RETURN TRUE END;
  r := a * b; RETURN FALSE
END Mul;

PROCEDURE Sub (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF a > b THEN r := a - b ELSE r := 0 END;
  RETURN FALSE
END Sub;

PROCEDURE Div (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF b = 0 THEN r := 0 ELSE r := a DIV b END;
  RETURN FALSE
END Div;

PROCEDURE Mod (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF b = 0 THEN r := a ELSE r := a MOD b END;
  RETURN FALSE
END Mod;

PROCEDURE Pow (a, e: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, base, k: LONGCARD;
BEGIN
  IF e = 0 THEN r := 1; RETURN FALSE END;
  IF a = 0 THEN r := 0; RETURN FALSE END;
  IF a = 1 THEN r := 1; RETURN FALSE END;
  IF e >= 64 THEN RETURN TRUE END;
  acc := 1; base := a; k := e;
  LOOP
    IF ODD(k) THEN
      IF Mul(acc, base, acc) THEN RETURN TRUE END
    END;
    k := k DIV 2;
    IF k = 0 THEN EXIT END;
    IF Mul(base, base, base) THEN RETURN TRUE END
  END;
  r := acc; RETURN FALSE
END Pow;

PROCEDURE Min (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a < b THEN RETURN a ELSE RETURN b END
END Min;

PROCEDURE Max (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a < b THEN RETURN b ELSE RETURN a END
END Max;

PROCEDURE Gcd (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, y, t: LONGCARD;
BEGIN
  x := a; y := b;
  WHILE y # 0 DO t := x MOD y; x := y; y := t END;
  r := x; RETURN FALSE
END Gcd;

PROCEDURE Lcm (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  g: LONGCARD;
BEGIN
  IF (a = 0) OR (b = 0) THEN r := 0; RETURN FALSE END;
  IF Gcd(a, b, g) THEN RETURN TRUE END;
  RETURN Mul(a DIV g, b, r)
END Lcm;

PROCEDURE Fact (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i: LONGCARD;
BEGIN
  IF n > 20 THEN RETURN TRUE END;
  acc := 1; i := 2;
  WHILE i <= n DO acc := acc * i; INC(i) END;
  r := acc; RETURN FALSE
END Fact;

PROCEDURE Choose (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  c, i, g, num, den, t, kk: LONGCARD;
BEGIN
  IF k > n THEN r := 0; RETURN FALSE END;
  kk := k;
  IF kk > n - kk THEN kk := n - kk END;
  c := 1; i := 1;
  WHILE i <= kk DO
    num := n - kk + i; den := i;
    IF Gcd(c, den, g) THEN RETURN TRUE END;
    c := c DIV g; den := den DIV g;
    IF Gcd(num, den, g) THEN RETURN TRUE END;
    num := num DIV g;
    IF Mul(c, num, t) THEN RETURN TRUE END;
    c := t; INC(i)
  END;
  r := c; RETURN FALSE
END Choose;

PROCEDURE Sqrt (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, bit, m: LONGCARD;
BEGIN
  m := n; x := 0; bit := 4611686018427387904;   (* 2^62 *)
  WHILE bit > m DO bit := bit DIV 4 END;
  WHILE bit # 0 DO
    IF m >= x + bit THEN m := m - (x + bit); x := x DIV 2 + bit ELSE x := x DIV 2 END;
    bit := bit DIV 4
  END;
  r := x; RETURN FALSE
END Sqrt;

PROCEDURE MinFac (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  d: LONGCARD;
BEGIN
  IF n = 0 THEN r := 2; RETURN FALSE END;
  IF n = 1 THEN r := 1; RETURN FALSE END;
  IF n MOD 2 = 0 THEN r := 2; RETURN FALSE END;
  d := 3;
  WHILE d <= n DIV d DO
    IF n MOD d = 0 THEN r := d; RETURN FALSE END;
    d := d + 2
  END;
  r := n; RETURN FALSE
END MinFac;

PROCEDURE IsPrime (n: LONGCARD) : LONGCARD;
VAR
  m: LONGCARD;
BEGIN
  IF n < 2 THEN RETURN 0 END;
  IF MinFac(n, m) THEN RETURN 0 END;
  IF m = n THEN RETURN 1 ELSE RETURN 0 END
END IsPrime;

PROCEDURE Dvd (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a = 0 THEN
    IF b = 0 THEN RETURN 1 ELSE RETURN 0 END
  END;
  IF b MOD a = 0 THEN RETURN 1 ELSE RETURN 0 END
END Dvd;

PROCEDURE Fib (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, y, z, i: LONGCARD;
BEGIN
  IF n > 93 THEN RETURN TRUE END;
  x := 0; y := 1; i := 0;
  WHILE i < n DO
    (* y = fib(i+2) would exceed MAX(LONGCARD) only on the last step for n = 93: skip it there *)
    IF i + 1 < n THEN z := x + y ELSE z := 0 END;
    x := y; y := z; INC(i)
  END;
  r := x; RETURN FALSE
END Fib;

PROCEDURE Log (b, n: LONGCARD) : LONGCARD;
VAR
  k, m: LONGCARD;
BEGIN
  IF b <= 1 THEN RETURN 0 END;
  k := 0; m := n;
  WHILE m >= b DO m := m DIV b; INC(k) END;
  RETURN k
END Log;

PROCEDURE Log2 (n: LONGCARD) : LONGCARD;
BEGIN
  RETURN Log(2, n)
END Log2;

PROCEDURE PadicVal (p, n: LONGCARD) : LONGCARD;
VAR
  k, m: LONGCARD;
BEGIN
  IF (p <= 1) OR (n = 0) THEN RETURN 0 END;
  k := 0; m := n;
  WHILE m MOD p = 0 DO m := m DIV p; INC(k) END;
  RETURN k
END PadicVal;

PROCEDURE BigOmega (n: LONGCARD) : LONGCARD;
VAR
  k, m, d: LONGCARD;
BEGIN
  IF n <= 1 THEN RETURN 0 END;
  k := 0; m := n; d := 2;
  WHILE d <= m DIV d DO
    WHILE m MOD d = 0 DO m := m DIV d; INC(k) END;
    INC(d)
  END;
  IF m > 1 THEN INC(k) END;
  RETURN k
END BigOmega;

PROCEDURE PfNth (n, k: LONGCARD) : LONGCARD;
VAR
  m, d, j: LONGCARD;
BEGIN
  IF n <= 1 THEN RETURN 0 END;
  m := n; d := 2; j := k;
  WHILE d <= m DIV d DO
    WHILE m MOD d = 0 DO
      IF j = 0 THEN RETURN d END;
      m := m DIV d; DEC(j)
    END;
    INC(d)
  END;
  IF (m > 1) AND (j = 0) THEN RETURN m END;
  RETURN 0
END PfNth;

PROCEDURE DigAt (b, n, k: LONGCARD) : LONGCARD;
VAR
  m, j: LONGCARD;
BEGIN
  IF b = 0 THEN
    IF k = 0 THEN RETURN n END;
    RETURN 0
  END;
  IF b = 1 THEN
    IF k < n THEN RETURN 1 END;
    RETURN 0
  END;
  m := n; j := k;
  WHILE (j > 0) AND (m > 0) DO m := m DIV b; DEC(j) END;
  RETURN m MOD b
END DigAt;

PROCEDURE DigSum (b, n: LONGCARD) : LONGCARD;
VAR
  s, m: LONGCARD;
BEGIN
  IF b <= 1 THEN RETURN n END;
  s := 0; m := n;
  WHILE m > 0 DO s := s + m MOD b; m := m DIV b END;
  RETURN s
END DigSum;

PROCEDURE DigLen (b, n: LONGCARD) : LONGCARD;
VAR
  k, m: LONGCARD;
BEGIN
  IF b = 0 THEN
    IF n = 0 THEN RETURN 0 ELSE RETURN 1 END
  END;
  IF b = 1 THEN RETURN n END;
  k := 0; m := n;
  WHILE m > 0 DO m := m DIV b; INC(k) END;
  RETURN k
END DigLen;

PROCEDURE DigRev (b, n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, t, m: LONGCARD;
BEGIN
  IF b <= 1 THEN r := n; RETURN FALSE END;
  acc := 0; m := n;
  WHILE m > 0 DO
    IF Mul(acc, b, t) THEN RETURN TRUE END;
    IF Add(t, m MOD b, acc) THEN RETURN TRUE END;
    m := m DIV b
  END;
  r := acc; RETURN FALSE
END DigRev;

PROCEDURE NatAbs (a: LONGINT) : LONGCARD;
BEGIN
  IF a < 0 THEN RETURN VAL(LONGCARD, -(a + 1)) + 1 ELSE RETURN VAL(LONGCARD, a) END
END NatAbs;

PROCEDURE ToNat (a: LONGINT) : LONGCARD;
BEGIN
  IF a < 0 THEN RETURN 0 ELSE RETURN VAL(LONGCARD, a) END
END ToNat;

PROCEDURE ISign (a: LONGINT) : LONGINT;
BEGIN
  IF a > 0 THEN RETURN 1 ELSIF a < 0 THEN RETURN -1 ELSE RETURN 0 END
END ISign;

PROCEDURE OfNat (x: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF x > VAL(LONGCARD, MAX(LONGINT)) THEN RETURN TRUE END;
  r := VAL(LONGINT, x); RETURN FALSE
END OfNat;

PROCEDURE INeg (a: LONGINT; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF a = MIN(LONGINT) THEN RETURN TRUE END;
  r := -a; RETURN FALSE
END INeg;

PROCEDURE IAdd (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF (b > 0) AND (a > MAX(LONGINT) - b) THEN RETURN TRUE END;
  IF (b < 0) AND (a < MIN(LONGINT) - b) THEN RETURN TRUE END;
  r := a + b; RETURN FALSE
END IAdd;

PROCEDURE ISub (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF (b < 0) AND (a > MAX(LONGINT) + b) THEN RETURN TRUE END;
  IF (b > 0) AND (a < MIN(LONGINT) + b) THEN RETURN TRUE END;
  r := a - b; RETURN FALSE
END ISub;

PROCEDURE IMul (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
VAR
  p, lim: LONGCARD;
  neg: BOOLEAN;
BEGIN
  neg := (a < 0) # (b < 0);
  IF Mul(NatAbs(a), NatAbs(b), p) THEN RETURN TRUE END;
  lim := VAL(LONGCARD, MAX(LONGINT));
  IF NOT neg THEN
    IF p > lim THEN RETURN TRUE END;
    r := VAL(LONGINT, p); RETURN FALSE
  END;
  IF p > lim + 1 THEN RETURN TRUE END;
  IF p = lim + 1 THEN r := MIN(LONGINT) ELSE r := -VAL(LONGINT, p) END;
  RETURN FALSE
END IMul;

PROCEDURE IPow (a: LONGINT; e: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR
  acc, base: LONGINT;
  k: LONGCARD;
BEGIN
  IF e = 0 THEN r := 1; RETURN FALSE END;
  IF (a = 0) OR (a = 1) THEN r := a; RETURN FALSE END;
  IF a = -1 THEN
    IF ODD(e) THEN r := -1 ELSE r := 1 END;
    RETURN FALSE
  END;
  IF e >= 64 THEN RETURN TRUE END;
  acc := 1; base := a; k := e;
  LOOP
    IF ODD(k) THEN
      IF IMul(acc, base, acc) THEN RETURN TRUE END
    END;
    k := k DIV 2;
    IF k = 0 THEN EXIT END;
    IF IMul(base, base, base) THEN RETURN TRUE END
  END;
  r := acc; RETURN FALSE
END IPow;

PROCEDURE Xor (a, b: LONGCARD) : LONGCARD;
VAR
  r, p, x, y: LONGCARD; i: CARDINAL;
BEGIN
  r := 0; p := 1; x := a; y := b; i := 0;
  WHILE i < 64 DO
    IF ODD(x) # ODD(y) THEN r := r + p END;
    x := x DIV 2; y := y DIV 2;
    IF i < 63 THEN p := p * 2 END;
    INC(i)
  END;
  RETURN r
END Xor;

END LM2Nat.
