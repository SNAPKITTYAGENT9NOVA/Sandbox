(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Poly;

IMPORT Rat;

VAR
  t1, t2, t3: T;                       (* workspaces (each ≈ 100 KB) kept off the stack *)

PROCEDURE Normalize (VAR p: T);
BEGIN
  WHILE (p.deg >= 0) AND Rat.IsZero(p.c[p.deg]) DO DEC(p.deg) END
END Normalize;

PROCEDURE Zero (VAR p: T);
VAR i: CARDINAL;
BEGIN
  p.deg := -1;
  FOR i := 0 TO MaxDeg DO Rat.FromInt(p.c[i], 0) END
END Zero;

PROCEDURE Const (VAR q: Rat.T; VAR p: T);
BEGIN
  Zero(p); p.c[0] := q; p.deg := 0; Normalize(p)
END Const;

PROCEDURE ConstInt (k: LONGINT; VAR p: T);
BEGIN
  Zero(p); Rat.FromInt(p.c[0], k); p.deg := 0; Normalize(p)
END ConstInt;

PROCEDURE Monomial (VAR q: Rat.T; k: CARDINAL; VAR p: T) : BOOLEAN;
BEGIN
  Zero(p);
  IF Rat.IsZero(q) THEN RETURN TRUE END;
  IF k > MaxDeg THEN RETURN FALSE END;
  p.c[k] := q; p.deg := VAL(INTEGER, k);
  RETURN TRUE
END Monomial;

PROCEDURE SetCoeff (VAR p: T; k: CARDINAL; VAR q: Rat.T) : BOOLEAN;
BEGIN
  IF k > MaxDeg THEN RETURN Rat.IsZero(q) END;
  p.c[k] := q;
  IF VAL(INTEGER, k) > p.deg THEN p.deg := VAL(INTEGER, k) END;
  Normalize(p);
  RETURN TRUE
END SetCoeff;

PROCEDURE IsZero (VAR p: T) : BOOLEAN;
BEGIN
  RETURN p.deg < 0
END IsZero;

PROCEDURE NatDegree (VAR p: T) : CARDINAL;
BEGIN
  IF p.deg < 0 THEN RETURN 0 END;
  RETURN VAL(CARDINAL, p.deg)
END NatDegree;

PROCEDURE Coeff (VAR p: T; k: CARDINAL; VAR q: Rat.T);
BEGIN
  IF VAL(INTEGER, k) > p.deg THEN Rat.FromInt(q, 0) ELSE q := p.c[k] END
END Coeff;

PROCEDURE LeadingCoeff (VAR p: T; VAR q: Rat.T);
BEGIN
  IF p.deg < 0 THEN Rat.FromInt(q, 0) ELSE q := p.c[p.deg] END
END LeadingCoeff;

PROCEDURE IsMonic (VAR p: T) : BOOLEAN;
VAR one: Rat.T;
BEGIN
  Rat.FromInt(one, 1);
  RETURN (p.deg >= 0) AND Rat.Equal(p.c[p.deg], one)
END IsMonic;

PROCEDURE Equal (VAR a, b: T) : BOOLEAN;
VAR i: INTEGER;
BEGIN
  IF a.deg # b.deg THEN RETURN FALSE END;
  i := 0;
  WHILE i <= a.deg DO
    IF NOT Rat.Equal(a.c[i], b.c[i]) THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Equal;

PROCEDURE Add (VAR a, b, r: T) : BOOLEAN;
VAR i, d: INTEGER; x, y: Rat.T;
BEGIN
  IF a.deg > b.deg THEN d := a.deg ELSE d := b.deg END;
  i := 0;
  WHILE i <= d DO
    Coeff(a, VAL(CARDINAL, i), x); Coeff(b, VAL(CARDINAL, i), y);
    IF NOT Rat.Add(x, y, r.c[i]) THEN RETURN FALSE END;
    INC(i)
  END;
  WHILE i <= MaxDeg DO Rat.FromInt(r.c[i], 0); INC(i) END;
  r.deg := d; Normalize(r);
  RETURN TRUE
END Add;

PROCEDURE Neg (VAR a, r: T);
VAR i: INTEGER;
BEGIN
  r.deg := a.deg; i := 0;
  WHILE i <= MaxDeg DO Rat.Neg(a.c[i], r.c[i]); INC(i) END
END Neg;

PROCEDURE Sub (VAR a, b, r: T) : BOOLEAN;
BEGIN
  Neg(b, t1);
  RETURN Add(a, t1, r)
END Sub;

PROCEDURE Scale (VAR q: Rat.T; VAR a, r: T) : BOOLEAN;
VAR i: INTEGER;
BEGIN
  r.deg := a.deg; i := 0;
  WHILE i <= MaxDeg DO
    IF i <= a.deg THEN
      IF NOT Rat.Mul(q, a.c[i], r.c[i]) THEN RETURN FALSE END
    ELSE Rat.FromInt(r.c[i], 0) END;
    INC(i)
  END;
  Normalize(r);
  RETURN TRUE
END Scale;

PROCEDURE Mul (VAR a, b, r: T) : BOOLEAN;
VAR i, j: INTEGER; p: Rat.T;
BEGIN
  Zero(t2);
  IF (a.deg < 0) OR (b.deg < 0) THEN r := t2; RETURN TRUE END;
  IF a.deg + b.deg > MaxDeg THEN RETURN FALSE END;
  i := 0;
  WHILE i <= a.deg DO
    j := 0;
    WHILE j <= b.deg DO
      IF NOT Rat.Mul(a.c[i], b.c[j], p) OR NOT Rat.Add(t2.c[i + j], p, t2.c[i + j]) THEN
        RETURN FALSE
      END;
      INC(j)
    END;
    INC(i)
  END;
  t2.deg := a.deg + b.deg; Normalize(t2);
  r := t2; RETURN TRUE
END Mul;

PROCEDURE Pow (VAR a: T; e: CARDINAL; VAR r: T) : BOOLEAN;
VAR acc, base: T; k: CARDINAL;
BEGIN
  ConstInt(1, acc); base := a; k := e;
  WHILE k > 0 DO
    IF ODD(k) THEN
      IF NOT Mul(acc, base, acc) THEN RETURN FALSE END
    END;
    k := k DIV 2;
    IF k > 0 THEN
      IF NOT Mul(base, base, base) THEN RETURN FALSE END
    END
  END;
  r := acc; RETURN TRUE
END Pow;

PROCEDURE Eval (VAR p: T; VAR x, r: Rat.T) : BOOLEAN;
VAR acc: Rat.T; i: INTEGER;
BEGIN
  Rat.FromInt(acc, 0); i := p.deg;
  WHILE i >= 0 DO                                     (* Horner *)
    IF NOT Rat.Mul(acc, x, acc) OR NOT Rat.Add(acc, p.c[i], acc) THEN RETURN FALSE END;
    DEC(i)
  END;
  r := acc; RETURN TRUE
END Eval;

PROCEDURE IsRoot (VAR p: T; VAR x: Rat.T) : BOOLEAN;
VAR v: Rat.T;
BEGIN
  RETURN Eval(p, x, v) AND Rat.IsZero(v)
END IsRoot;

PROCEDURE Derivative (VAR a, r: T) : BOOLEAN;
VAR i: INTEGER; k: Rat.T;
BEGIN
  Zero(t1);
  i := 1;
  WHILE i <= a.deg DO
    Rat.FromInt(k, VAL(LONGINT, i));
    IF NOT Rat.Mul(k, a.c[i], t1.c[i - 1]) THEN RETURN FALSE END;
    INC(i)
  END;
  t1.deg := a.deg - 1; Normalize(t1);
  r := t1; RETURN TRUE
END Derivative;

PROCEDURE Comp (VAR p, q, r: T) : BOOLEAN;
(* Horner in ℚ[X]: ((c_d q + c_{d-1}) q + …) *)
VAR acc, cst: T; i: INTEGER;
BEGIN
  Zero(acc); i := p.deg;
  WHILE i >= 0 DO
    IF NOT Mul(acc, q, acc) THEN RETURN FALSE END;
    Const(p.c[i], cst);
    IF NOT Add(acc, cst, acc) THEN RETURN FALSE END;
    DEC(i)
  END;
  r := acc; RETURN TRUE
END Comp;

PROCEDURE DivMod (VAR a, b, q, m: T) : BOOLEAN;
VAR rem, quo: T; lead, f, p: Rat.T; shift, i: INTEGER;
BEGIN
  IF b.deg < 0 THEN m := a; Zero(q); RETURN TRUE END;     (* p / 0 = 0, p % 0 = p *)
  rem := a; Zero(quo);
  lead := b.c[b.deg];
  WHILE rem.deg >= b.deg DO
    shift := rem.deg - b.deg;
    IF NOT Rat.Div(rem.c[rem.deg], lead, f) THEN RETURN FALSE END;
    quo.c[shift] := f;
    IF shift > quo.deg THEN quo.deg := shift END;
    i := 0;
    WHILE i <= b.deg DO
      IF NOT Rat.Mul(f, b.c[i], p) OR NOT Rat.Sub(rem.c[i + shift], p, rem.c[i + shift]) THEN
        RETURN FALSE
      END;
      INC(i)
    END;
    Rat.FromInt(rem.c[rem.deg], 0);                   (* exact cancellation of the top term *)
    Normalize(rem)
  END;
  Normalize(quo);
  q := quo; m := rem; RETURN TRUE
END DivMod;

PROCEDURE Gcd (VAR a, b, g: T) : BOOLEAN;
VAR x, y, q, r: T; lead, inv: Rat.T;
BEGIN
  x := a; y := b;
  WHILE y.deg >= 0 DO
    IF NOT DivMod(x, y, q, r) THEN RETURN FALSE END;
    x := y; y := r
  END;
  IF x.deg < 0 THEN g := x; RETURN TRUE END;
  LeadingCoeff(x, lead); Rat.Inv(lead, inv);
  RETURN Scale(inv, x, g)
END Gcd;

PROCEDURE Put (VAR s: ARRAY OF CHAR; VAR k: CARDINAL; c: CHAR) : BOOLEAN;
BEGIN
  IF k > HIGH(s) THEN RETURN FALSE END;
  s[k] := c; INC(k); RETURN TRUE
END Put;

PROCEDURE ToText (VAR p: T; VAR s: ARRAY OF CHAR) : BOOLEAN;
VAR k, j: CARDINAL; i: INTEGER; buf: ARRAY [0..5200] OF CHAR;
BEGIN
  k := 0;
  IF NOT Put(s, k, '[') THEN RETURN FALSE END;
  i := 0;
  WHILE i <= p.deg DO
    IF i > 0 THEN
      IF NOT Put(s, k, ',') OR NOT Put(s, k, ' ') THEN RETURN FALSE END
    END;
    IF NOT Rat.ToText(p.c[i], buf) THEN RETURN FALSE END;
    j := 0;
    WHILE buf[j] # 0C DO
      IF NOT Put(s, k, buf[j]) THEN RETURN FALSE END;
      INC(j)
    END;
    INC(i)
  END;
  RETURN Put(s, k, ']') AND Put(s, k, 0C)
END ToText;

END Poly.
