(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE BigNat;
(* Schoolbook addition, subtraction and multiplication; Knuth's Algorithm D (TAOCP vol. 2,
   4.3.1) for division; binary exponentiation; Euclid's algorithm; Newton's method for the
   square root. Digit products are formed in LONGCARD (64 bits), which never overflows for
   base 2^32 digits. *)

CONST
  Base = 100000000H;                            (* 2^32 *)

TYPE
  Buf = ARRAY [0..2 * Capacity] OF CARDINAL;

PROCEDURE Norm (VAR a: T);
BEGIN
  WHILE (a.n > 0) AND (a.d[a.n - 1] = 0) DO DEC(a.n) END
END Norm;

PROCEDURE FromNat (VAR r: T; x: LONGCARD);
BEGIN
  r.d[0] := VAL(CARDINAL, x MOD Base);
  r.d[1] := VAL(CARDINAL, x DIV Base);
  r.n := 2; Norm(r)
END FromNat;

PROCEDURE ToNat (VAR a: T; VAR x: LONGCARD) : BOOLEAN;
BEGIN
  IF a.n > 2 THEN RETURN FALSE END;
  x := 0;
  IF a.n > 0 THEN x := VAL(LONGCARD, a.d[0]) END;
  IF a.n > 1 THEN x := x + VAL(LONGCARD, a.d[1]) * Base END;
  RETURN TRUE
END ToNat;

PROCEDURE IsZero (VAR a: T) : BOOLEAN;
BEGIN
  RETURN a.n = 0
END IsZero;

PROCEDURE Cmp (VAR a, b: T) : INTEGER;
VAR
  i: CARDINAL;
BEGIN
  IF a.n # b.n THEN
    IF a.n < b.n THEN RETURN -1 ELSE RETURN 1 END
  END;
  i := a.n;
  WHILE i > 0 DO
    IF a.d[i - 1] # b.d[i - 1] THEN
      IF a.d[i - 1] < b.d[i - 1] THEN RETURN -1 ELSE RETURN 1 END
    END;
    DEC(i)
  END;
  RETURN 0
END Cmp;

PROCEDURE Equal (VAR a, b: T) : BOOLEAN;
BEGIN
  RETURN Cmp(a, b) = 0
END Equal;

PROCEDURE BitLength (VAR a: T) : CARDINAL;
VAR
  top, k: CARDINAL;
BEGIN
  IF a.n = 0 THEN RETURN 0 END;
  top := a.d[a.n - 1]; k := 0;
  WHILE top # 0 DO top := top DIV 2; INC(k) END;
  RETURN (a.n - 1) * 32 + k
END BitLength;

PROCEDURE IsOdd (VAR a: T) : BOOLEAN;
BEGIN
  RETURN (a.n > 0) AND ODD(a.d[0])
END IsOdd;

PROCEDURE Digit (VAR a: T; i: CARDINAL) : LONGCARD;
BEGIN
  IF i < a.n THEN RETURN VAL(LONGCARD, a.d[i]) END;
  RETURN 0
END Digit;

PROCEDURE Add (VAR a, b, r: T) : BOOLEAN;
VAR
  t: T; i, m: CARDINAL; c: LONGCARD;
BEGIN
  IF a.n > b.n THEN m := a.n ELSE m := b.n END;
  c := 0; i := 0;
  WHILE i < m DO
    c := c + Digit(a, i) + Digit(b, i);
    t.d[i] := VAL(CARDINAL, c MOD Base); c := c DIV Base;
    INC(i)
  END;
  IF c # 0 THEN
    IF m = Capacity THEN RETURN FALSE END;
    t.d[m] := VAL(CARDINAL, c); INC(m)
  END;
  t.n := m; r := t; RETURN TRUE
END Add;

PROCEDURE Sub (VAR a, b, r: T);
VAR
  t: T; i: CARDINAL; c: LONGINT;
BEGIN
  IF Cmp(a, b) <= 0 THEN r.n := 0; RETURN END;
  c := 0; i := 0;
  WHILE i < a.n DO
    c := c + VAL(LONGINT, Digit(a, i)) - VAL(LONGINT, Digit(b, i));
    IF c < 0 THEN
      t.d[i] := VAL(CARDINAL, c + VAL(LONGINT, Base)); c := -1
    ELSE
      t.d[i] := VAL(CARDINAL, c); c := 0
    END;
    INC(i)
  END;
  t.n := a.n; Norm(t); r := t
END Sub;

PROCEDURE Mul (VAR a, b, r: T) : BOOLEAN;
VAR
  buf: Buf; i, j, m: CARDINAL; c, p: LONGCARD;
BEGIN
  IF (a.n = 0) OR (b.n = 0) THEN r.n := 0; RETURN TRUE END;
  m := a.n + b.n;
  i := 0; WHILE i < m DO buf[i] := 0; INC(i) END;
  i := 0;
  WHILE i < a.n DO
    c := 0; j := 0;
    WHILE j < b.n DO
      p := VAL(LONGCARD, a.d[i]) * VAL(LONGCARD, b.d[j]) + VAL(LONGCARD, buf[i + j]) + c;
      buf[i + j] := VAL(CARDINAL, p MOD Base); c := p DIV Base;
      INC(j)
    END;
    buf[i + b.n] := VAL(CARDINAL, c);
    INC(i)
  END;
  WHILE (m > 0) AND (buf[m - 1] = 0) DO DEC(m) END;
  IF m > Capacity THEN RETURN FALSE END;
  i := 0; WHILE i < m DO r.d[i] := buf[i]; INC(i) END;
  r.n := m; RETURN TRUE
END Mul;

PROCEDURE MulSmall (VAR a: T; k: CARDINAL; VAR r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  FromNat(t, VAL(LONGCARD, k));
  RETURN Mul(a, t, r)
END MulSmall;

PROCEDURE AddSmall (VAR a: T; k: CARDINAL; VAR r: T) : BOOLEAN;
VAR
  t: T;
BEGIN
  FromNat(t, VAL(LONGCARD, k));
  RETURN Add(a, t, r)
END AddSmall;

PROCEDURE P2 (s: CARDINAL) : LONGCARD;          (* 2^s, s < 64 *)
VAR
  v: LONGCARD;
BEGIN
  v := 1; WHILE s > 0 DO v := v * 2; DEC(s) END; RETURN v
END P2;

PROCEDURE Shl (x, s: CARDINAL) : CARDINAL;       (* (x << s) mod 2^32 *)
BEGIN
  RETURN VAL(CARDINAL, (VAL(LONGCARD, x) * P2(s)) MOD Base)
END Shl;

PROCEDURE Shr (x, s: CARDINAL) : CARDINAL;       (* x >> s, s <= 32 *)
BEGIN
  RETURN VAL(CARDINAL, VAL(LONGCARD, x) DIV P2(s))
END Shr;

PROCEDURE FDiv32 (t: LONGINT) : LONGINT;         (* floor(t / 2^32) *)
BEGIN
  IF t >= 0 THEN RETURN t DIV VAL(LONGINT, Base) END;
  RETURN -((-(t + 1)) DIV VAL(LONGINT, Base)) - 1
END FDiv32;

PROCEDURE DivModSmall (VAR a: T; k: CARDINAL; VAR q: T; VAR m: CARDINAL);
VAR
  t: T; i: CARDINAL; rem, cur: LONGCARD;
BEGIN
  rem := 0; i := a.n;
  WHILE i > 0 DO
    cur := rem * Base + VAL(LONGCARD, a.d[i - 1]);
    t.d[i - 1] := VAL(CARDINAL, cur DIV VAL(LONGCARD, k));
    rem := cur MOD VAL(LONGCARD, k);
    DEC(i)
  END;
  t.n := a.n; Norm(t); q := t; m := VAL(CARDINAL, rem)
END DivModSmall;

PROCEDURE DivMod (VAR a, b, q, m: T);
VAR
  qq, rr: T; un, vn: Buf;
  na, nb, s, i, top, small: CARDINAL; j: INTEGER;
  num, qhat, rhat, p, c: LONGCARD;
  t, k: LONGINT;
BEGIN
  IF b.n = 0 THEN rr := a; q.n := 0; m := rr; RETURN END;
  IF Cmp(a, b) < 0 THEN rr := a; q.n := 0; m := rr; RETURN END;
  na := a.n; nb := b.n;
  IF nb = 1 THEN
    DivModSmall(a, b.d[0], qq, small);
    q := qq; FromNat(m, VAL(LONGCARD, small)); RETURN
  END;
  (* normalise so that the top digit of the divisor has its high bit set *)
  s := 0; top := b.d[nb - 1];
  WHILE top < 80000000H DO top := top * 2; INC(s) END;
  i := nb - 1;
  WHILE i > 0 DO
    IF s > 0 THEN vn[i] := Shl(b.d[i], s) + Shr(b.d[i - 1], 32 - s) ELSE vn[i] := b.d[i] END;
    DEC(i)
  END;
  vn[0] := Shl(b.d[0], s);
  IF s > 0 THEN un[na] := Shr(a.d[na - 1], 32 - s) ELSE un[na] := 0 END;
  i := na - 1;
  WHILE i > 0 DO
    IF s > 0 THEN un[i] := Shl(a.d[i], s) + Shr(a.d[i - 1], 32 - s) ELSE un[i] := a.d[i] END;
    DEC(i)
  END;
  un[0] := Shl(a.d[0], s);
  j := VAL(INTEGER, na - nb);
  WHILE j >= 0 DO
    num := VAL(LONGCARD, un[VAL(CARDINAL, j) + nb]) * Base + VAL(LONGCARD, un[VAL(CARDINAL, j) + nb - 1]);
    qhat := num DIV VAL(LONGCARD, vn[nb - 1]);
    rhat := num MOD VAL(LONGCARD, vn[nb - 1]);
    LOOP
      IF (qhat < Base) AND
         (qhat * VAL(LONGCARD, vn[nb - 2]) <= rhat * Base + VAL(LONGCARD, un[VAL(CARDINAL, j) + nb - 2])) THEN
        EXIT
      END;
      DEC(qhat); rhat := rhat + VAL(LONGCARD, vn[nb - 1]);
      IF rhat >= Base THEN EXIT END
    END;
    (* multiply and subtract *)
    k := 0; i := 0;
    WHILE i < nb DO
      p := qhat * VAL(LONGCARD, vn[i]);
      t := VAL(LONGINT, un[i + VAL(CARDINAL, j)]) - k - VAL(LONGINT, p MOD Base);
      un[i + VAL(CARDINAL, j)] := VAL(CARDINAL, t - FDiv32(t) * VAL(LONGINT, Base));
      k := VAL(LONGINT, p DIV Base) - FDiv32(t);
      INC(i)
    END;
    t := VAL(LONGINT, un[VAL(CARDINAL, j) + nb]) - k;
    un[VAL(CARDINAL, j) + nb] := VAL(CARDINAL, t - FDiv32(t) * VAL(LONGINT, Base));
    qq.d[VAL(CARDINAL, j)] := VAL(CARDINAL, qhat);
    IF t < 0 THEN
      (* qhat was one too large: add the divisor back *)
      qq.d[VAL(CARDINAL, j)] := VAL(CARDINAL, qhat - 1);
      c := 0; i := 0;
      WHILE i < nb DO
        c := c + VAL(LONGCARD, un[i + VAL(CARDINAL, j)]) + VAL(LONGCARD, vn[i]);
        un[i + VAL(CARDINAL, j)] := VAL(CARDINAL, c MOD Base); c := c DIV Base;
        INC(i)
      END;
      un[VAL(CARDINAL, j) + nb] := VAL(CARDINAL, (VAL(LONGCARD, un[VAL(CARDINAL, j) + nb]) + c) MOD Base)
    END;
    DEC(j)
  END;
  qq.n := na - nb + 1; Norm(qq);
  (* un-normalise the remainder *)
  i := 0;
  WHILE i < nb DO
    IF s > 0 THEN rr.d[i] := Shr(un[i], s) + Shl(un[i + 1], 32 - s) ELSE rr.d[i] := un[i] END;
    INC(i)
  END;
  rr.n := nb; Norm(rr);
  q := qq; m := rr
END DivMod;

PROCEDURE Div (VAR a, b, r: T);
VAR
  q, m: T;
BEGIN
  DivMod(a, b, q, m); r := q
END Div;

PROCEDURE Mod (VAR a, b, r: T);
VAR
  q, m: T;
BEGIN
  DivMod(a, b, q, m); r := m
END Mod;

PROCEDURE Pow (VAR a: T; e: LONGCARD; VAR r: T) : BOOLEAN;
VAR
  acc, base: T; k: LONGCARD;
BEGIN
  FromNat(acc, 1);
  IF e = 0 THEN r := acc; RETURN TRUE END;
  IF a.n = 0 THEN r.n := 0; RETURN TRUE END;
  IF (a.n = 1) AND (a.d[0] = 1) THEN r := acc; RETURN TRUE END;
  (* a >= 2: the result has at least e bits *)
  IF e > VAL(LONGCARD, MaxBits) THEN RETURN FALSE END;
  base := a; k := e;
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

PROCEDURE Gcd (VAR a, b, r: T);
VAR
  x, y, t: T;
BEGIN
  x := a; y := b;
  WHILE y.n # 0 DO
    Mod(x, y, t); x := y; y := t
  END;
  r := x
END Gcd;

PROCEDURE Lcm (VAR a, b, r: T) : BOOLEAN;
VAR
  g, q: T;
BEGIN
  IF (a.n = 0) OR (b.n = 0) THEN r.n := 0; RETURN TRUE END;
  Gcd(a, b, g);
  Div(a, g, q);
  RETURN Mul(q, b, r)
END Lcm;

PROCEDURE Sqrt (VAR a, r: T);
(* Newton's iteration x' = (x + a / x) / 2 from an upper bound; stops when it no longer decreases *)
VAR
  x, y, q, two: T; bits: CARDINAL; ok: BOOLEAN;
BEGIN
  IF a.n = 0 THEN r.n := 0; RETURN END;
  bits := BitLength(a);
  FromNat(two, 2);
  FromNat(x, 1);
  ok := Pow(two, VAL(LONGCARD, (bits + 1) DIV 2), x);     (* 2^ceil(bits/2) >= sqrt(a) *)
  LOOP
    Div(a, x, q);
    ok := Add(x, q, y);
    Div(y, two, y);
    IF Cmp(y, x) >= 0 THEN EXIT END;
    x := y
  END;
  r := x
END Sqrt;

PROCEDURE ToDecimal (VAR a: T; VAR s: ARRAY OF CHAR) : BOOLEAN;
VAR
  buf: ARRAY [0..2600] OF CHAR; t: T; n, i, dgt: CARDINAL;
BEGIN
  IF a.n = 0 THEN
    IF HIGH(s) < 1 THEN RETURN FALSE END;
    s[0] := '0'; s[1] := 0C; RETURN TRUE
  END;
  t := a; n := 0;
  WHILE t.n # 0 DO
    DivModSmall(t, 10, t, dgt);
    buf[n] := CHR(ORD('0') + dgt); INC(n)
  END;
  IF n > HIGH(s) THEN RETURN FALSE END;
  i := 0;
  WHILE i < n DO s[i] := buf[n - 1 - i]; INC(i) END;
  s[n] := 0C;
  RETURN TRUE
END ToDecimal;

PROCEDURE FromDecimal (s: ARRAY OF CHAR; VAR r: T) : BOOLEAN;
VAR
  t: T; i: CARDINAL;
BEGIN
  t.n := 0; i := 0;
  IF (HIGH(s) = 0) AND (s[0] = 0C) THEN RETURN FALSE END;
  IF s[0] = 0C THEN RETURN FALSE END;
  WHILE (i <= HIGH(s)) AND (s[i] # 0C) DO
    IF (s[i] < '0') OR (s[i] > '9') THEN RETURN FALSE END;
    IF NOT MulSmall(t, 10, t) THEN RETURN FALSE END;
    IF NOT AddSmall(t, ORD(s[i]) - ORD('0'), t) THEN RETURN FALSE END;
    INC(i)
  END;
  r := t; RETURN TRUE
END FromDecimal;

END BigNat.
