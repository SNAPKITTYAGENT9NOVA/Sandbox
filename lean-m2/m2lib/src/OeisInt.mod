(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE OeisInt;

IMPORT NatArith, NumberTheory, Combinatorics, Digits, BigNat, BigInt, Rat, Matrix;

VAR
  rm: Matrix.RatMat;                   (* large workspaces kept off the stack *)
  im: Matrix.IntMat;

(* ---- conversions ---- *)

PROCEDURE NatToInt (VAR a: BigNat.T; VAR r: BigInt.T);
BEGIN
  BigInt.OfBigNat(a, r)
END NatToInt;

PROCEDURE NatToRat (VAR a: BigNat.T; VAR r: Rat.T);
VAR i: BigInt.T;
BEGIN
  BigInt.OfBigNat(a, i); Rat.OfBigInt(i, r)
END NatToRat;

PROCEDURE IntToRat (VAR a: BigInt.T; VAR r: Rat.T);
BEGIN
  Rat.OfBigInt(a, r)
END IntToRat;

PROCEDURE NumNatAbs (VAR q: Rat.T; VAR r: LONGCARD) : BOOLEAN;   (* q.num.natAbs *)
VAR i: BigInt.T; b: BigNat.T;
BEGIN
  Rat.Num(q, i); BigInt.NatAbs(i, b);
  RETURN BigNat.ToNat(b, r)
END NumNatAbs;

PROCEDURE DenNat (VAR q: Rat.T; VAR r: LONGCARD) : BOOLEAN;      (* q.den *)
VAR b: BigNat.T;
BEGIN
  Rat.Den(q, b);
  RETURN BigNat.ToNat(b, r)
END DenNat;

PROCEDURE ChooseRat (n, k: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR b: BigNat.T;
BEGIN
  IF NOT Combinatorics.ChooseBig(n, k, b) THEN RETURN FALSE END;
  NatToRat(b, r); RETURN TRUE
END ChooseRat;

PROCEDURE ChooseInt (n, k: LONGCARD; VAR r: BigInt.T) : BOOLEAN;
VAR b: BigNat.T;
BEGIN
  IF NOT Combinatorics.ChooseBig(n, k, b) THEN RETURN FALSE END;
  NatToInt(b, r); RETURN TRUE
END ChooseInt;

PROCEDURE SubI (a, b: LONGINT; VAR r: LONGINT) : BOOLEAN;
BEGIN
  IF (b < 0) AND (a > MAX(LONGINT) + b) THEN RETURN FALSE END;
  IF (b > 0) AND (a < MIN(LONGINT) + b) THEN RETURN FALSE END;
  r := a - b; RETURN TRUE
END SubI;

(* a(m + k) = ∑_{i<k} c[i] · a(m + i), with a(0..k-1) = init; computed in BigInt *)
PROCEDURE LinRec (VAR init, c: ARRAY OF LONGINT; n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR w: ARRAY [0..3] OF BigInt.T; k, i: CARDINAL; m: LONGCARD; s, t, ci: BigInt.T;
BEGIN
  k := HIGH(init) + 1;
  IF n < VAL(LONGCARD, k) THEN r := init[VAL(CARDINAL, n)]; RETURN TRUE END;
  FOR i := 0 TO k - 1 DO BigInt.FromInt(w[i], init[i]) END;
  m := VAL(LONGCARD, k);
  WHILE m <= n DO
    BigInt.FromInt(s, 0);
    FOR i := 0 TO k - 1 DO
      BigInt.FromInt(ci, c[i]);
      IF NOT BigInt.Mul(ci, w[i], t) OR NOT BigInt.Add(s, t, s) THEN RETURN FALSE END
    END;
    FOR i := 0 TO k - 2 DO w[i] := w[i + 1] END;
    w[k - 1] := s;
    INC(m)
  END;
  RETURN BigInt.ToInt(w[k - 1], r)
END LinRec;

(* ---------------------------------------------------------------------------------- *)

PROCEDURE A003162 (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR num, d, c0, c1, den, t: Rat.T; k: LONGCARD;
BEGIN
  Rat.FromInt(num, 0); k := 0;
  WHILE k <= n DIV 2 DO
    IF NOT ChooseRat(n, k, c1) THEN RETURN FALSE END;
    IF k = 0 THEN Rat.FromInt(c0, 0)
    ELSIF NOT ChooseRat(n, k - 1, c0) THEN RETURN FALSE END;
    IF NOT Rat.Sub(c1, c0, d) OR NOT Rat.Pow(d, 3, t) OR NOT Rat.Add(num, t, num) THEN
      RETURN FALSE
    END;
    INC(k)
  END;
  IF NOT ChooseRat(n, n DIV 2, den) THEN RETURN FALSE END;
  RETURN Rat.Div(num, den, r)
END A003162;

PROCEDURE A007406 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, t: Rat.T; k, k2: LONGCARD;
BEGIN
  Rat.FromInt(s, 0); k := 1;
  WHILE k <= n DO
    IF NOT NatArith.Mul(k, k, k2) OR NOT Rat.MakeSmall(1, k2, t) OR NOT Rat.Add(s, t, s) THEN
      RETURN FALSE
    END;
    INC(k)
  END;
  RETURN NumNatAbs(s, r)
END A007406;

PROCEDURE A046969 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR b, k, q: Rat.T; m: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF n > 128 THEN RETURN FALSE END;
  m := 2 * n;
  IF NOT Combinatorics.Bernoulli(m, b) THEN RETURN FALSE END;
  Rat.FromNat(k, m * (m - 1));
  IF NOT Rat.Div(b, k, q) THEN RETURN FALSE END;
  RETURN DenNat(q, r)
END A046969;

PROCEDURE A060841 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR i, j: CARDINAL; l: LONGCARD; d, inv: Rat.T; num: BigInt.T;
BEGIN
  IF n > Matrix.MaxN THEN RETURN FALSE END;
  rm.n := VAL(CARDINAL, n);
  i := 0;
  WHILE i < rm.n DO
    j := 0;
    WHILE j < rm.n DO
      IF NOT NumberTheory.Lcm(VAL(LONGCARD, i + 1), VAL(LONGCARD, j + 1), l)
         OR NOT Rat.MakeSmall(1, l, rm.a[i, j]) THEN RETURN FALSE END;
      INC(j)
    END;
    INC(i)
  END;
  IF NOT Matrix.RatDet(rm, d) THEN RETURN FALSE END;
  Rat.Inv(d, inv);
  Rat.Num(inv, num);
  RETURN BigInt.ToInt(num, r)
END A060841;

PROCEDURE A064169 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR h: Rat.T; num, den: BigInt.T; d: BigNat.T;
BEGIN
  IF NOT Combinatorics.Harmonic(n, h) THEN RETURN FALSE END;
  Rat.Num(h, num); Rat.Den(h, d); NatToInt(d, den);
  IF NOT BigInt.Sub(num, den, num) THEN RETURN FALSE END;
  RETURN BigInt.ToInt(num, r)
END A064169;

PROCEDURE A067857 (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR s, h, mu, t, f: Rat.T; d: LONGCARD; fb: BigNat.T;
BEGIN
  IF n = 0 THEN Rat.FromInt(r, 0); RETURN TRUE END;
  Rat.FromInt(s, 0); d := 1;
  WHILE d <= n DO
    IF n MOD d = 0 THEN
      IF NOT Combinatorics.Harmonic(d, h) THEN RETURN FALSE END;
      Rat.FromInt(mu, VAL(LONGINT, NumberTheory.Moebius(n DIV d)));
      IF NOT Rat.Mul(mu, h, t) OR NOT Rat.Add(s, t, s) THEN RETURN FALSE END
    END;
    INC(d)
  END;
  IF NOT Combinatorics.FactorialBig(n, fb) THEN RETURN FALSE END;
  NatToRat(fb, f);
  RETURN Rat.Mul(f, s, r)
END A067857;

PROCEDURE A071524 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR i, j: CARDINAL; v: LONGCARD; d: BigInt.T;
BEGIN
  IF n > Matrix.MaxN THEN RETURN FALSE END;
  Matrix.IntZero(VAL(CARDINAL, n), im);
  i := 0;
  WHILE i < im.n DO
    j := 0;
    WHILE j < im.n DO
      v := VAL(LONGCARD, (i + 1) * (i + 1) + (j + 1) * (j + 1));
      IF NumberTheory.IsPrime(v) THEN im.a[i, j] := 1 ELSE im.a[i, j] := 0 END;
      INC(j)
    END;
    INC(i)
  END;
  IF NOT Matrix.IntDet(im, d) THEN RETURN FALSE END;
  RETURN BigInt.ToInt(d, r)
END A071524;

PROCEDURE A071532 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
(* (-1)^(3^k / 2^k): the parity of ⌊3^k / 2^k⌋ is bit k of 3^k *)
VAR x: BigNat.T; k: LONGCARD; s: LONGINT; w, b: CARDINAL; odd: BOOLEAN;
BEGIN
  IF n > 5000 THEN RETURN FALSE END;
  BigNat.FromNat(x, 1); s := 0; k := 1;
  WHILE k <= n DO
    IF NOT BigNat.MulSmall(x, 3, x) THEN RETURN FALSE END;
    w := VAL(CARDINAL, k DIV 32); b := VAL(CARDINAL, k MOD 32);
    odd := (w < x.n) AND NatArith.TestBit(VAL(LONGCARD, x.d[w]), VAL(LONGCARD, b));
    IF odd THEN s := s - 1 ELSE s := s + 1 END;
    INC(k)
  END;
  r := -s; RETURN TRUE
END A071532;

PROCEDURE A080326 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, t: Rat.T; k: LONGCARD; mu: INTEGER;
BEGIN
  Rat.FromInt(s, 0); k := 1;
  WHILE k <= n DO
    mu := NumberTheory.Moebius(k);
    IF mu = 1 THEN Rat.FromNat(t, k)
    ELSIF mu = 0 THEN Rat.FromInt(t, 1)
    ELSIF NOT Rat.MakeSmall(1, k, t) THEN RETURN FALSE END;
    IF NOT Rat.Add(s, t, s) THEN RETURN FALSE END;
    INC(k)
  END;
  RETURN DenNat(s, r)
END A080326;

PROCEDURE A087455 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR init, c: ARRAY [0..1] OF LONGINT;
BEGIN
  init[0] := 1; init[1] := 1; c[0] := -3; c[1] := 2;
  RETURN LinRec(init, c, n, r)
END A087455;

PROCEDURE A093818 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR h: Rat.T; num: BigInt.T; a, f, g: BigNat.T;
BEGIN
  IF NOT Combinatorics.Harmonic(n, h) OR NOT Combinatorics.FactorialBig(n, f) THEN RETURN FALSE END;
  Rat.Num(h, num); BigInt.NatAbs(num, a);
  BigNat.Gcd(a, f, g);
  RETURN BigNat.ToNat(g, r)
END A093818;

PROCEDURE A100434 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR init, c: ARRAY [0..3] OF LONGINT;
BEGIN
  init[0] := 3; init[1] := 4; init[2] := -17; init[3] := -24;
  c[0] := -1; c[1] := 0; c[2] := -6; c[3] := 0;
  RETURN LinRec(init, c, n, r)
END A100434;

PROCEDURE A100434c (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR init, c: ARRAY [0..3] OF LONGINT;
BEGIN
  init[0] := 1; init[1] := -3; init[2] := -7; init[3] := 17;
  c[0] := -1; c[1] := 0; c[2] := -6; c[3] := 0;
  RETURN LinRec(init, c, n, r)
END A100434c;

PROCEDURE A100434d (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR init, c: ARRAY [0..3] OF LONGINT;
BEGIN
  init[0] := 2; init[1] := 4; init[2] := -10; init[3] := -24;
  c[0] := -1; c[1] := 0; c[2] := -6; c[3] := 0;
  RETURN LinRec(init, c, n, r)
END A100434d;

PROCEDURE A109074 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, b: BigNat.T; num: BigInt.T; q: Rat.T;
BEGIN
  IF NOT Combinatorics.ChooseBig(NatArith.Sub(6 * n, 2), 2 * n, a)
     OR NOT Combinatorics.ChooseBig(NatArith.Sub(4 * n, 1), 2 * n, b)
     OR NOT BigNat.MulSmall(b, 2, b) THEN RETURN FALSE END;
  NatToInt(a, num);
  IF NOT Rat.Make(num, b, q) THEN RETURN FALSE END;
  RETURN NumNatAbs(q, r)
END A109074;

PROCEDURE A110566 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR l, t, d, q: BigNat.T; h: Rat.T; k: LONGCARD;
BEGIN
  BigNat.FromNat(l, 1); k := 1;
  WHILE k <= n DO
    BigNat.FromNat(t, k);
    IF NOT BigNat.Lcm(l, t, l) THEN RETURN FALSE END;
    INC(k)
  END;
  IF NOT Combinatorics.Harmonic(n, h) THEN RETURN FALSE END;
  Rat.Den(h, d);
  BigNat.Div(l, d, q);
  RETURN BigNat.ToNat(q, r)
END A110566;

PROCEDURE Rec113 (i2, i3, c1, c0: LONGINT; n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR init, c: ARRAY [0..3] OF LONGINT;
BEGIN
  init[0] := -1; init[1] := 4; init[2] := i2; init[3] := i3;
  c[0] := c0; c[1] := c1; c[2] := 0; c[3] := -4;
  RETURN LinRec(init, c, n, r)
END Rec113;

PROCEDURE A113250 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN Rec113(32, 64, 64, 256, n, r)
END A113250;

PROCEDURE A113252 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN Rec113(92, 784, 144, 1296, n, r)
END A113252;

PROCEDURE A113254 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN Rec113(176, 3136, 256, 4096, n, r)
END A113254;

PROCEDURE A113255 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN Rec113(227, 5329, 324, 6561, n, r)
END A113255;

PROCEDURE A116150 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, p3, p2, three, mtwo: BigInt.T; j: LONGCARD; b: BigNat.T;
BEGIN
  BigInt.FromInt(s, 0); BigInt.FromInt(p3, 1); BigInt.FromInt(p2, 1);
  BigInt.FromInt(three, 3); BigInt.FromInt(mtwo, -2);
  j := 1;
  WHILE j <= n DO
    IF NOT BigInt.Mul(p3, three, p3) OR NOT BigInt.Mul(p2, mtwo, p2)
       OR NOT BigInt.Add(s, p3, s) OR NOT BigInt.Add(s, p2, s) THEN RETURN FALSE END;
    INC(j)
  END;
  BigInt.ToNat(s, b);                                  (* Int.toNat *)
  RETURN BigNat.ToNat(b, r)
END A116150;

PROCEDURE A129365 (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR num, den, t, f: BigNat.T; j, k: LONGCARD; numI: BigInt.T;
BEGIN
  BigNat.FromNat(num, 1); BigNat.FromNat(den, 1);
  j := 1;
  WHILE j <= n DO
    k := 1;
    WHILE k <= n DO
      BigNat.FromNat(t, NumberTheory.Gcd(j, k));
      IF NOT BigNat.Mul(num, t, num) THEN RETURN FALSE END;
      INC(k)
    END;
    INC(j)
  END;
  k := 1;
  WHILE k <= n DO
    IF NOT Combinatorics.FactorialBig(n DIV k, f) OR NOT BigNat.Pow(f, k, t)
       OR NOT BigNat.Mul(den, t, den) THEN RETURN FALSE END;
    INC(k)
  END;
  NatToInt(num, numI);
  RETURN Rat.Make(numI, den, r)
END A129365;

PROCEDURE A176477 (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR a, idx, t, u, c, num, den: Rat.T; m, i3, poly: LONGCARD;
BEGIN
  IF n = 0 THEN Rat.FromInt(r, 0); RETURN TRUE END;
  Rat.FromInt(a, 2); m := 2;
  WHILE m <= n DO
    IF (m > 1000000) THEN RETURN FALSE END;          (* keeps the cubic coefficients in 64 bits *)
    i3 := m * m * m;
    poly := 21 * i3 + 22 * m * m + 8 * m + 1;
    Rat.FromNat(idx, 32 * i3);
    IF NOT Rat.Mul(idx, a, num) THEN RETURN FALSE END;
    IF NOT ChooseRat(2 * m - 1, m, c) OR NOT Rat.Pow(c, 4, c) THEN RETURN FALSE END;
    Rat.FromNat(u, poly);
    IF NOT Rat.Mul(u, c, t) OR NOT Rat.Add(num, t, num) THEN RETURN FALSE END;
    Rat.FromNat(den, 2 * m + 1);
    IF NOT Rat.Pow(den, 3, den) OR NOT Rat.Div(num, den, a) THEN RETURN FALSE END;
    INC(m)
  END;
  r := a; RETURN TRUE
END A176477;

PROCEDURE SignedBinomSum (n: LONGCARD; base: LONGINT; VAR r: LONGINT) : BOOLEAN;
(* ∑_{k ≤ n} base^k · C(n,k)^2 · C(n-k,k)^2 *)
VAR s, p, b, c1, c2, t: BigInt.T; k: LONGCARD;
BEGIN
  BigInt.FromInt(s, 0); BigInt.FromInt(p, 1); BigInt.FromInt(b, base);
  k := 0;
  WHILE k <= n DO
    IF NOT ChooseInt(n, k, c1) OR NOT ChooseInt(n - k, k, c2)
       OR NOT BigInt.Mul(c1, c1, c1) OR NOT BigInt.Mul(c2, c2, c2)
       OR NOT BigInt.Mul(c1, c2, t) OR NOT BigInt.Mul(t, p, t)
       OR NOT BigInt.Add(s, t, s) OR NOT BigInt.Mul(p, b, p) THEN RETURN FALSE END;
    INC(k)
  END;
  RETURN BigInt.ToInt(s, r)
END SignedBinomSum;

PROCEDURE A179524 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN SignedBinomSum(n, -4, r)
END A179524;

PROCEDURE A179537 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
BEGIN
  RETURN SignedBinomSum(n, -16, r)
END A179537;

PROCEDURE A180017 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR s3, s2: LONGCARD;
BEGIN
  s3 := Digits.Sum(3, n); s2 := Digits.Sum(2, n);
  IF s3 >= s2 THEN r := VAL(LONGINT, s3 - s2) ELSE r := -VAL(LONGINT, s2 - s3) END;
  RETURN TRUE
END A180017;

PROCEDURE IntXor (a, b: LONGINT) : LONGINT;
(* ofNat m ^ ofNat n = ofNat (m ^^^ n);  ofNat m ^ -[n+1] = -[m ^^^ n + 1];
   -[m+1] ^ ofNat n = -[m ^^^ n + 1];   -[m+1] ^ -[n+1] = ofNat (m ^^^ n) *)
VAR m, n, k: LONGCARD;
BEGIN
  IF a >= 0 THEN m := VAL(LONGCARD, a) ELSE m := VAL(LONGCARD, -(a + 1)) END;
  IF b >= 0 THEN n := VAL(LONGCARD, b) ELSE n := VAL(LONGCARD, -(b + 1)) END;
  k := NatArith.Xor(m, n);
  IF (a >= 0) = (b >= 0) THEN RETURN VAL(LONGINT, k) END;
  RETURN -VAL(LONGINT, k) - 1
END IntXor;

PROCEDURE A182510 (n: LONGCARD; VAR r: LONGINT) : BOOLEAN;
VAR a0, a1, a2: LONGINT; m: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF n >= 4611686018427387904 THEN RETURN FALSE END;
  a0 := 0; a1 := 1; m := 2;
  WHILE m <= n DO
    IF NOT SubI(IntXor(a1, VAL(LONGINT, m)), a0, a2) THEN RETURN FALSE END;
    a0 := a1; a1 := a2; INC(m)
  END;
  r := a1; RETURN TRUE
END A182510;

PROCEDURE A357513 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, c1, c2, t, k3: Rat.T; k: LONGCARD;
BEGIN
  Rat.FromInt(s, 0); k := 1;
  WHILE k <= n DO
    IF NOT ChooseRat(n, k, c1) OR NOT ChooseRat(n + k, k, c2)
       OR NOT Rat.Mul(c1, c2, t) OR NOT Rat.Pow(t, 2, t) THEN RETURN FALSE END;
    Rat.FromNat(k3, k);
    IF NOT Rat.Pow(k3, 3, k3) OR NOT Rat.Div(t, k3, t) OR NOT Rat.Add(s, t, s) THEN RETURN FALSE END;
    INC(k)
  END;
  RETURN NumNatAbs(s, r)
END A357513;

END OeisInt.
