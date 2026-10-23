(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE NatArith;

PROCEDURE Add (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF a > MaxNat - b THEN RETURN FALSE END;
  r := a + b; RETURN TRUE
END Add;

PROCEDURE Mul (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF (a # 0) AND (b > MaxNat DIV a) THEN RETURN FALSE END;
  r := a * b; RETURN TRUE
END Mul;

PROCEDURE Pow (a, e: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, base, k: LONGCARD;
BEGIN
  IF e = 0 THEN r := 1; RETURN TRUE END;
  IF a <= 1 THEN r := a; RETURN TRUE END;
  acc := 1; base := a; k := e;
  LOOP
    IF ODD(k) THEN
      IF NOT Mul(acc, base, acc) THEN RETURN FALSE END
    END;
    k := k DIV 2;
    IF k = 0 THEN EXIT END;
    IF NOT Mul(base, base, base) THEN RETURN FALSE END
  END;
  r := acc; RETURN TRUE
END Pow;

PROCEDURE Sub (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF b >= a THEN RETURN 0 END;
  RETURN a - b
END Sub;

PROCEDURE Div (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF b = 0 THEN RETURN 0 END;
  RETURN a DIV b
END Div;

PROCEDURE Mod (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF b = 0 THEN RETURN a END;
  RETURN a MOD b
END Mod;

PROCEDURE Pred (a: LONGCARD) : LONGCARD;
BEGIN
  IF a = 0 THEN RETURN 0 END;
  RETURN a - 1
END Pred;

PROCEDURE Min (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a <= b THEN RETURN a END;
  RETURN b
END Min;

PROCEDURE Max (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a >= b THEN RETURN a END;
  RETURN b
END Max;

PROCEDURE Dist (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a >= b THEN RETURN a - b END;
  RETURN b - a
END Dist;

PROCEDURE Dvd (a, b: LONGCARD) : BOOLEAN;
BEGIN
  IF a = 0 THEN RETURN b = 0 END;
  RETURN b MOD a = 0
END Dvd;

PROCEDURE IsEven (a: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NOT ODD(a)
END IsEven;

PROCEDURE IsOdd (a: LONGCARD) : BOOLEAN;
BEGIN
  RETURN ODD(a)
END IsOdd;

PROCEDURE Sqrt (n: LONGCARD) : LONGCARD;
(* bitwise integer square root: exact for all 64-bit n, no floating point *)
VAR
  x, bit, t: LONGCARD;
BEGIN
  x := 0; t := n;
  bit := 4611686018427387904;                (* 2^62 *)
  WHILE bit > t DO bit := bit DIV 4 END;
  WHILE bit # 0 DO
    IF t >= x + bit THEN
      t := t - (x + bit);
      x := x DIV 2 + bit
    ELSE
      x := x DIV 2
    END;
    bit := bit DIV 4
  END;
  RETURN x
END Sqrt;

PROCEDURE IsSquare (n: LONGCARD) : BOOLEAN;
VAR
  r: LONGCARD;
BEGIN
  r := Sqrt(n);
  RETURN r * r = n
END IsSquare;

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

PROCEDURE Clog (b, n: LONGCARD) : LONGCARD;
(* least k with n <= b^k, computed without overflow: b^k is compared as a running product
   that stops as soon as it reaches n *)
VAR
  k, p: LONGCARD;
BEGIN
  IF (b <= 1) OR (n <= 1) THEN RETURN 0 END;
  k := 0; p := 1;
  WHILE p < n DO
    IF p > MaxNat DIV b THEN RETURN k + 1 END;   (* next power exceeds every 64-bit n *)
    p := p * b; INC(k)
  END;
  RETURN k
END Clog;

PROCEDURE Xor (a, b: LONGCARD) : LONGCARD;
VAR
  r, bit, x, y: LONGCARD;
BEGIN
  r := 0; bit := 1; x := a; y := b;
  WHILE (x # 0) OR (y # 0) DO
    IF ODD(x) # ODD(y) THEN r := r + bit END;
    x := x DIV 2; y := y DIV 2;
    IF (x # 0) OR (y # 0) THEN bit := bit * 2 END
  END;
  RETURN r
END Xor;

PROCEDURE LAnd (a, b: LONGCARD) : LONGCARD;
VAR
  r, bit, x, y: LONGCARD;
BEGIN
  r := 0; bit := 1; x := a; y := b;
  WHILE (x # 0) AND (y # 0) DO
    IF ODD(x) AND ODD(y) THEN r := r + bit END;
    x := x DIV 2; y := y DIV 2;
    IF (x # 0) AND (y # 0) THEN bit := bit * 2 END
  END;
  RETURN r
END LAnd;

PROCEDURE LOr (a, b: LONGCARD) : LONGCARD;
VAR
  r, bit, x, y: LONGCARD;
BEGIN
  r := 0; bit := 1; x := a; y := b;
  WHILE (x # 0) OR (y # 0) DO
    IF ODD(x) OR ODD(y) THEN r := r + bit END;
    x := x DIV 2; y := y DIV 2;
    IF (x # 0) OR (y # 0) THEN bit := bit * 2 END
  END;
  RETURN r
END LOr;

PROCEDURE TestBit (n, i: LONGCARD) : BOOLEAN;
VAR
  x, k: LONGCARD;
BEGIN
  IF i >= 64 THEN RETURN FALSE END;
  x := n; k := i;
  WHILE k > 0 DO x := x DIV 2; DEC(k) END;
  RETURN ODD(x)
END TestBit;

PROCEDURE PopCount (n: LONGCARD) : LONGCARD;
VAR
  c, x: LONGCARD;
BEGIN
  c := 0; x := n;
  WHILE x # 0 DO
    IF ODD(x) THEN INC(c) END;
    x := x DIV 2
  END;
  RETURN c
END PopCount;

PROCEDURE ShiftLeft (a, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  p: LONGCARD;
BEGIN
  IF a = 0 THEN r := 0; RETURN TRUE END;
  IF NOT Pow(2, k, p) THEN RETURN FALSE END;
  RETURN Mul(a, p, r)
END ShiftLeft;

PROCEDURE ShiftRight (a, k: LONGCARD) : LONGCARD;
VAR
  x, j: LONGCARD;
BEGIN
  IF k >= 64 THEN RETURN 0 END;
  x := a; j := k;
  WHILE j > 0 DO x := x DIV 2; DEC(j) END;
  RETURN x
END ShiftRight;

END NatArith.
