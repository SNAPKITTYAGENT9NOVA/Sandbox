(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Matrix;

IMPORT BigInt, Rat;

TYPE
  BigMat = ARRAY Index, Index OF BigInt.T;

VAR
  work: BigMat;                       (* Bareiss workspace (≈ 270 KB, kept off the stack) *)
  rw, rw2: RatMat;                    (* Gaussian elimination workspaces *)

PROCEDURE MulI (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
VAR x, y, z: BigInt.T;
BEGIN
  BigInt.FromInt(x, a); BigInt.FromInt(y, b);
  IF NOT BigInt.Mul(x, y, z) THEN RETURN FALSE END;
  RETURN BigInt.ToInt(z, r)
END MulI;

PROCEDURE AddI (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF (b > 0) AND (a > MAX(LONGINT) - b) THEN RETURN FALSE END;
  IF (b < 0) AND (a < MIN(LONGINT) - b) THEN RETURN FALSE END;
  r := a + b; RETURN TRUE
END AddI;

PROCEDURE IntZero (n: CARDINAL; VAR m: IntMat);
VAR i, j: CARDINAL;
BEGIN
  m.n := n;
  FOR i := 0 TO MaxN - 1 DO FOR j := 0 TO MaxN - 1 DO m.a[i, j] := 0 END END
END IntZero;

PROCEDURE IntIdentity (n: CARDINAL; VAR m: IntMat);
VAR i: CARDINAL;
BEGIN
  IntZero(n, m);
  i := 0;
  WHILE i < n DO m.a[i, i] := 1; INC(i) END
END IntIdentity;

PROCEDURE IntEqual (VAR a, b: IntMat) : BOOLEAN;
VAR i, j: CARDINAL;
BEGIN
  IF a.n # b.n THEN RETURN FALSE END;
  i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO
      IF a.a[i, j] # b.a[i, j] THEN RETURN FALSE END;
      INC(j)
    END;
    INC(i)
  END;
  RETURN TRUE
END IntEqual;

PROCEDURE IntTranspose (VAR a, r: IntMat);
VAR i, j: CARDINAL; t: LONGINT;
BEGIN
  r.n := a.n;
  i := 0;
  WHILE i < a.n DO
    r.a[i, i] := a.a[i, i];
    j := i + 1;
    WHILE j < a.n DO
      t := a.a[i, j]; r.a[i, j] := a.a[j, i]; r.a[j, i] := t;
      INC(j)
    END;
    INC(i)
  END
END IntTranspose;

PROCEDURE IntAdd (VAR a, b, r: IntMat) : BOOLEAN;
VAR i, j: CARDINAL;
BEGIN
  IF a.n # b.n THEN RETURN FALSE END;
  r.n := a.n; i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO
      IF NOT AddI(a.a[i, j], b.a[i, j], r.a[i, j]) THEN RETURN FALSE END;
      INC(j)
    END;
    INC(i)
  END;
  RETURN TRUE
END IntAdd;

PROCEDURE IntMul (VAR a, b, r: IntMat) : BOOLEAN;
VAR t: IntMat; i, j, k: CARDINAL; s, p: LONGINT;
BEGIN
  IF a.n # b.n THEN RETURN FALSE END;
  IntZero(a.n, t);
  i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO
      s := 0; k := 0;
      WHILE k < a.n DO
        IF NOT MulI(a.a[i, k], b.a[k, j], p) OR NOT AddI(s, p, s) THEN RETURN FALSE END;
        INC(k)
      END;
      t.a[i, j] := s;
      INC(j)
    END;
    INC(i)
  END;
  r := t; RETURN TRUE
END IntMul;

PROCEDURE IntPow (VAR a: IntMat; e: LONGCARD; VAR r: IntMat) : BOOLEAN;
VAR acc, base: IntMat; k: LONGCARD;
BEGIN
  IntIdentity(a.n, acc); base := a; k := e;
  WHILE k > 0 DO
    IF ODD(k) THEN
      IF NOT IntMul(acc, base, acc) THEN RETURN FALSE END
    END;
    k := k DIV 2;
    IF k > 0 THEN
      IF NOT IntMul(base, base, base) THEN RETURN FALSE END
    END
  END;
  r := acc; RETURN TRUE
END IntPow;

PROCEDURE IntTrace (VAR a: IntMat; VAR t: LONGINT) : BOOLEAN;
VAR i: CARDINAL; s: LONGINT;
BEGIN
  s := 0; i := 0;
  WHILE i < a.n DO
    IF NOT AddI(s, a.a[i, i], s) THEN RETURN FALSE END;
    INC(i)
  END;
  t := s; RETURN TRUE
END IntTrace;

PROCEDURE IntDet (VAR a: IntMat; VAR d: BigInt.T) : BOOLEAN;
(* Bareiss: M[i,j] := (M[k,k] M[i,j] - M[i,k] M[k,j]) / prev, exact at every step;
   row swaps flip the sign. *)
VAR n, i, j, k, piv: CARDINAL; prev, t1, t2, q, tmp: BigInt.T; neg: BOOLEAN;
BEGIN
  n := a.n;
  IF n = 0 THEN BigInt.FromInt(d, 1); RETURN TRUE END;
  IF n = 1 THEN BigInt.FromInt(d, a.a[0, 0]); RETURN TRUE END;
  FOR i := 0 TO n - 1 DO
    FOR j := 0 TO n - 1 DO BigInt.FromInt(work[i, j], a.a[i, j]) END
  END;
  BigInt.FromInt(prev, 1); neg := FALSE;
  FOR k := 0 TO n - 2 DO
    IF BigInt.IsZero(work[k, k]) THEN
      piv := k + 1;
      WHILE (piv < n) AND BigInt.IsZero(work[piv, k]) DO INC(piv) END;
      IF piv = n THEN BigInt.FromInt(d, 0); RETURN TRUE END;
      FOR j := 0 TO n - 1 DO
        tmp := work[k, j]; work[k, j] := work[piv, j]; work[piv, j] := tmp
      END;
      neg := NOT neg
    END;
    FOR i := k + 1 TO n - 1 DO
      FOR j := k + 1 TO n - 1 DO
        IF NOT BigInt.Mul(work[k, k], work[i, j], t1) OR NOT BigInt.Mul(work[i, k], work[k, j], t2)
           OR NOT BigInt.Sub(t1, t2, t1) OR NOT BigInt.Div(t1, prev, q) THEN
          RETURN FALSE
        END;
        work[i, j] := q
      END
    END;
    prev := work[k, k]
  END;
  d := work[n - 1, n - 1];
  IF neg THEN BigInt.Neg(d, d) END;
  RETURN TRUE
END IntDet;

PROCEDURE ModMul (a, b, m: LONGCARD) : LONGCARD;   (* a, b < m < 2^62 *)
VAR r: LONGCARD;
BEGIN
  r := 0;
  WHILE b > 0 DO
    IF ODD(b) THEN r := (r + a) MOD m END;
    a := (a + a) MOD m; b := b DIV 2
  END;
  RETURN r
END ModMul;

PROCEDURE Reduce (x: LONGINT; m: LONGCARD) : LONGCARD;
VAR u: LONGCARD;
BEGIN
  IF x >= 0 THEN RETURN VAL(LONGCARD, x) MOD m END;
  u := (VAL(LONGCARD, -(x + 1)) + 1) MOD m;
  IF u = 0 THEN RETURN 0 END;
  RETURN m - u
END Reduce;

PROCEDURE MulMod (VAR a, b, r: IntMat; m: LONGCARD);
VAR t: IntMat; i, j, k: CARDINAL; s: LONGCARD;
BEGIN
  IntZero(a.n, t);
  FOR i := 0 TO a.n - 1 DO
    FOR j := 0 TO a.n - 1 DO
      s := 0;
      FOR k := 0 TO a.n - 1 DO
        s := (s + ModMul(VAL(LONGCARD, a.a[i, k]), VAL(LONGCARD, b.a[k, j]), m)) MOD m
      END;
      t.a[i, j] := VAL(LONGINT, s)
    END
  END;
  r := t
END MulMod;

PROCEDURE IntPowMod (VAR a: IntMat; e, m: LONGCARD; VAR r: IntMat) : BOOLEAN;
VAR acc, base: IntMat; i, j: CARDINAL; k: LONGCARD;
BEGIN
  IF (m = 0) OR (m >= 4611686018427387904) THEN RETURN FALSE END;
  IntIdentity(a.n, acc); base := a;
  i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO
      base.a[i, j] := VAL(LONGINT, Reduce(a.a[i, j], m));
      acc.a[i, j] := VAL(LONGINT, Reduce(acc.a[i, j], m));
      INC(j)
    END;
    INC(i)
  END;
  IF a.n = 0 THEN r := acc; RETURN TRUE END;
  k := e;
  WHILE k > 0 DO
    IF ODD(k) THEN MulMod(acc, base, acc, m) END;
    k := k DIV 2;
    IF k > 0 THEN MulMod(base, base, base, m) END
  END;
  r := acc; RETURN TRUE
END IntPowMod;

PROCEDURE RatFromInt (VAR a: IntMat; VAR r: RatMat);
VAR i, j: CARDINAL;
BEGIN
  r.n := a.n; i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO Rat.FromInt(r.a[i, j], a.a[i, j]); INC(j) END;
    INC(i)
  END
END RatFromInt;

PROCEDURE Eliminate (VAR w: RatMat; VAR det: Rat.T; VAR rank: CARDINAL) : BOOLEAN;
(* row-echelon form in place; det accumulates the pivots with swap signs (0 if singular) *)
VAR n, row, col, piv, i, j: CARDINAL; f, t: Rat.T; tmp: Rat.T;
BEGIN
  n := w.n; row := 0; rank := 0;
  Rat.FromInt(det, 1);
  col := 0;
  WHILE (col < n) AND (row < n) DO
    piv := row;
    WHILE (piv < n) AND Rat.IsZero(w.a[piv, col]) DO INC(piv) END;
    IF piv = n THEN
      Rat.FromInt(det, 0)                              (* zero column: singular *)
    ELSE
      IF piv # row THEN
        FOR j := 0 TO n - 1 DO
          tmp := w.a[row, j]; w.a[row, j] := w.a[piv, j]; w.a[piv, j] := tmp
        END;
        Rat.Neg(det, det)
      END;
      IF NOT Rat.Mul(det, w.a[row, col], det) THEN RETURN FALSE END;
      FOR i := row + 1 TO n - 1 DO
        IF NOT Rat.IsZero(w.a[i, col]) THEN
          IF NOT Rat.Div(w.a[i, col], w.a[row, col], f) THEN RETURN FALSE END;
          FOR j := col TO n - 1 DO
            IF NOT Rat.Mul(f, w.a[row, j], t) OR NOT Rat.Sub(w.a[i, j], t, w.a[i, j]) THEN
              RETURN FALSE
            END
          END
        END
      END;
      INC(row); INC(rank)
    END;
    INC(col)
  END;
  IF rank < n THEN Rat.FromInt(det, 0) END;
  RETURN TRUE
END Eliminate;

PROCEDURE RatDet (VAR a: RatMat; VAR d: Rat.T) : BOOLEAN;
VAR k: CARDINAL;
BEGIN
  IF a.n = 0 THEN Rat.FromInt(d, 1); RETURN TRUE END;
  rw := a;
  RETURN Eliminate(rw, d, k)
END RatDet;

PROCEDURE RatRank (VAR a: RatMat; VAR k: CARDINAL) : BOOLEAN;
VAR d: Rat.T;
BEGIN
  IF a.n = 0 THEN k := 0; RETURN TRUE END;
  rw := a;
  RETURN Eliminate(rw, d, k)
END RatRank;

PROCEDURE RatMul (VAR a, b, r: RatMat) : BOOLEAN;
VAR i, j, k: CARDINAL; s, p: Rat.T;
BEGIN
  IF a.n # b.n THEN RETURN FALSE END;
  rw.n := a.n;
  i := 0;
  WHILE i < a.n DO
    j := 0;
    WHILE j < a.n DO
      Rat.FromInt(s, 0); k := 0;
      WHILE k < a.n DO
        IF NOT Rat.Mul(a.a[i, k], b.a[k, j], p) OR NOT Rat.Add(s, p, s) THEN RETURN FALSE END;
        INC(k)
      END;
      rw.a[i, j] := s;
      INC(j)
    END;
    INC(i)
  END;
  r := rw; RETURN TRUE
END RatMul;

PROCEDURE RatInverse (VAR a, r: RatMat) : BOOLEAN;
(* Gauss–Jordan on [a | I]; rw holds a, rw2 holds the right half *)
VAR n, i, j, k, piv: CARDINAL; f, t, tmp: Rat.T;
BEGIN
  n := a.n; rw := a; rw2.n := n;
  FOR i := 0 TO MaxN - 1 DO
    FOR j := 0 TO MaxN - 1 DO
      IF i = j THEN Rat.FromInt(rw2.a[i, j], 1) ELSE Rat.FromInt(rw2.a[i, j], 0) END
    END
  END;
  IF n = 0 THEN r := rw2; RETURN TRUE END;
  FOR k := 0 TO n - 1 DO
    piv := k;
    WHILE (piv < n) AND Rat.IsZero(rw.a[piv, k]) DO INC(piv) END;
    IF piv = n THEN                                   (* singular: Lean's inverse is 0 *)
      r.n := n;
      FOR i := 0 TO MaxN - 1 DO FOR j := 0 TO MaxN - 1 DO Rat.FromInt(r.a[i, j], 0) END END;
      RETURN TRUE
    END;
    IF piv # k THEN
      FOR j := 0 TO n - 1 DO
        tmp := rw.a[k, j]; rw.a[k, j] := rw.a[piv, j]; rw.a[piv, j] := tmp;
        tmp := rw2.a[k, j]; rw2.a[k, j] := rw2.a[piv, j]; rw2.a[piv, j] := tmp
      END
    END;
    f := rw.a[k, k];
    FOR j := 0 TO n - 1 DO
      IF NOT Rat.Div(rw.a[k, j], f, rw.a[k, j]) OR NOT Rat.Div(rw2.a[k, j], f, rw2.a[k, j]) THEN
        RETURN FALSE
      END
    END;
    FOR i := 0 TO n - 1 DO
      IF (i # k) AND NOT Rat.IsZero(rw.a[i, k]) THEN
        f := rw.a[i, k];
        FOR j := 0 TO n - 1 DO
          IF NOT Rat.Mul(f, rw.a[k, j], t) OR NOT Rat.Sub(rw.a[i, j], t, rw.a[i, j]) THEN
            RETURN FALSE
          END;
          IF NOT Rat.Mul(f, rw2.a[k, j], t) OR NOT Rat.Sub(rw2.a[i, j], t, rw2.a[i, j]) THEN
            RETURN FALSE
          END
        END
      END
    END
  END;
  r := rw2; RETURN TRUE
END RatInverse;

END Matrix.
