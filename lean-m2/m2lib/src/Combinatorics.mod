(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Combinatorics;

IMPORT NatArith, NumberTheory, BigNat, BigInt, Rat;

PROCEDURE Factorial (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i: LONGCARD;
BEGIN
  acc := 1; i := 2;
  WHILE i <= n DO
    IF NOT NatArith.Mul(acc, i, acc) THEN RETURN FALSE END;
    INC(i)
  END;
  r := acc; RETURN TRUE
END Factorial;

PROCEDURE FactorialBig (n: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
VAR
  acc: BigNat.T; i: LONGCARD;
BEGIN
  BigNat.FromNat(acc, 1); i := 2;
  WHILE i <= n DO
    IF i > VAL(LONGCARD, MAX(CARDINAL)) THEN RETURN FALSE END;
    IF NOT BigNat.MulSmall(acc, VAL(CARDINAL, i), acc) THEN RETURN FALSE END;
    INC(i)
  END;
  r := acc; RETURN TRUE
END FactorialBig;

PROCEDURE DescFactorial (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i: LONGCARD;
BEGIN
  IF k > n THEN r := 0; RETURN TRUE END;
  acc := 1; i := 0;
  WHILE i < k DO
    IF NOT NatArith.Mul(acc, n - i, acc) THEN RETURN FALSE END;
    INC(i)
  END;
  r := acc; RETURN TRUE
END DescFactorial;

PROCEDURE AscFactorial (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i, f: LONGCARD;
BEGIN
  acc := 1; i := 0;
  WHILE i < k DO
    IF NOT NatArith.Add(n, i, f) THEN RETURN FALSE END;
    IF NOT NatArith.Mul(acc, f, acc) THEN RETURN FALSE END;
    INC(i)
  END;
  r := acc; RETURN TRUE
END AscFactorial;

PROCEDURE DoubleFactorial (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i: LONGCARD;
BEGIN
  acc := 1; i := n;
  WHILE i >= 2 DO
    IF NOT NatArith.Mul(acc, i, acc) THEN RETURN FALSE END;
    i := i - 2
  END;
  r := acc; RETURN TRUE
END DoubleFactorial;

PROCEDURE Choose (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* C(n, i) = C(n, i-1) * (n-i+1) / i, with the common factor removed first so that every
   intermediate is an exact binomial coefficient times at most i; overflow is reported only
   if the value itself, or such an intermediate, exceeds 64 bits *)
VAR
  c, i, kk, num, den, g: LONGCARD;
BEGIN
  IF k > n THEN r := 0; RETURN TRUE END;
  kk := k;
  IF n - k < kk THEN kk := n - k END;
  c := 1; i := 1;
  WHILE i <= kk DO
    num := n - kk + i; den := i;
    g := NumberTheory.Gcd(c, den); c := c DIV g; den := den DIV g;
    g := NumberTheory.Gcd(num, den); num := num DIV g; den := den DIV g;
    (* den is now 1: C(n,i) is an integer and gcd(c, den) = gcd(num, den) = 1 *)
    IF NOT NatArith.Mul(c, num, c) THEN RETURN FALSE END;
    c := c DIV den;
    INC(i)
  END;
  r := c; RETURN TRUE
END Choose;

PROCEDURE ChooseBig (n, k: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
VAR
  c, t: BigNat.T; i, kk: LONGCARD; rem: CARDINAL;
BEGIN
  IF k > n THEN r.n := 0; RETURN TRUE END;
  kk := k;
  IF n - k < kk THEN kk := n - k END;
  IF kk > VAL(LONGCARD, MAX(CARDINAL)) THEN RETURN FALSE END;
  BigNat.FromNat(c, 1); i := 1;
  WHILE i <= kk DO
    BigNat.FromNat(t, n - kk + i);
    IF NOT BigNat.Mul(c, t, c) THEN RETURN FALSE END;
    BigNat.DivModSmall(c, VAL(CARDINAL, i), c, rem);      (* exact: rem = 0 *)
    INC(i)
  END;
  r := c; RETURN TRUE
END ChooseBig;

PROCEDURE CentralBinom (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  m: LONGCARD;
BEGIN
  IF NOT NatArith.Mul(2, n, m) THEN RETURN FALSE END;
  RETURN Choose(m, n, r)
END CentralBinom;

PROCEDURE Multichoose (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  m: LONGCARD;
BEGIN
  IF (n = 0) THEN
    IF k = 0 THEN r := 1 ELSE r := 0 END;
    RETURN TRUE
  END;
  IF NOT NatArith.Add(n - 1, k, m) THEN RETURN FALSE END;
  RETURN Choose(m, k, r)
END Multichoose;

PROCEDURE Fib (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  a, b, t, i: LONGCARD;
BEGIN
  a := 0; b := 1; i := 0;
  WHILE i < n DO
    IF NOT NatArith.Add(a, b, t) THEN
      IF i + 1 = n THEN r := b; RETURN TRUE END;        (* fib n = b is still representable *)
      RETURN FALSE
    END;
    a := b; b := t; INC(i)
  END;
  r := a; RETURN TRUE
END Fib;

PROCEDURE FibBig (n: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
VAR
  a, b, t: BigNat.T; i: LONGCARD;
BEGIN
  BigNat.FromNat(a, 0); BigNat.FromNat(b, 1); i := 0;
  WHILE i < n DO
    IF NOT BigNat.Add(a, b, t) THEN
      IF i + 1 = n THEN r := b; RETURN TRUE END;
      RETURN FALSE
    END;
    a := b; b := t; INC(i)
  END;
  r := a; RETURN TRUE
END FibBig;

PROCEDURE Lucas (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  a, b, t, i: LONGCARD;
BEGIN
  a := 2; b := 1; i := 0;
  WHILE i < n DO
    IF NOT NatArith.Add(a, b, t) THEN
      IF i + 1 = n THEN r := b; RETURN TRUE END;
      RETURN FALSE
    END;
    a := b; b := t; INC(i)
  END;
  r := a; RETURN TRUE
END Lucas;

PROCEDURE Catalan (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  c: BigNat.T;
BEGIN
  IF NOT CatalanBig(n, c) THEN RETURN FALSE END;
  RETURN BigNat.ToNat(c, r)
END Catalan;

PROCEDURE CatalanBig (n: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
(* catalan (n+1) = catalan n * 2(2n+1) / (n+2), each step exact *)
VAR
  c: BigNat.T; i: LONGCARD; rem: CARDINAL;
BEGIN
  BigNat.FromNat(c, 1); i := 0;
  WHILE i < n DO
    IF 2 * (2 * i + 1) > VAL(LONGCARD, MAX(CARDINAL)) THEN RETURN FALSE END;
    IF NOT BigNat.MulSmall(c, VAL(CARDINAL, 2 * (2 * i + 1)), c) THEN RETURN FALSE END;
    BigNat.DivModSmall(c, VAL(CARDINAL, i + 2), c, rem);
    INC(i)
  END;
  r := c; RETURN TRUE
END CatalanBig;

PROCEDURE Partitions (n: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
(* Euler's pentagonal number theorem:
   p(m) = ∑_{k>=1} (-1)^(k+1) (p(m - k(3k-1)/2) + p(m - k(3k+1)/2)) *)
CONST
  Max = 2048;                                 (* the table lives on the stack: 2049 × 1 KiB *)
VAR
  p: ARRAY [0..Max] OF BigNat.T;
  m, k, g1, g2: LONGCARD;
  plus, minus: BigNat.T;
BEGIN
  IF n > Max THEN RETURN FALSE END;
  BigNat.FromNat(p[0], 1);
  m := 1;
  WHILE m <= n DO
    BigNat.FromNat(plus, 0); BigNat.FromNat(minus, 0);
    k := 1;
    LOOP
      g1 := k * (3 * k - 1) DIV 2;
      IF g1 > m THEN EXIT END;
      g2 := k * (3 * k + 1) DIV 2;
      IF ODD(k) THEN
        IF NOT BigNat.Add(plus, p[m - g1], plus) THEN RETURN FALSE END;
        IF (g2 <= m) AND NOT BigNat.Add(plus, p[m - g2], plus) THEN RETURN FALSE END
      ELSE
        IF NOT BigNat.Add(minus, p[m - g1], minus) THEN RETURN FALSE END;
        IF (g2 <= m) AND NOT BigNat.Add(minus, p[m - g2], minus) THEN RETURN FALSE END
      END;
      INC(k)
    END;
    BigNat.Sub(plus, minus, p[m]);
    INC(m)
  END;
  r := p[n]; RETURN TRUE
END Partitions;

PROCEDURE Derangements (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* numDerangements: d 0 = 1, d 1 = 0, d (n+2) = (n+1) (d n + d (n+1)) *)
VAR
  a, b, s, t, i: LONGCARD;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  a := 1; b := 0; i := 1;
  WHILE i < n DO
    IF NOT NatArith.Add(a, b, s) THEN RETURN FALSE END;
    IF NOT NatArith.Mul(i, s, t) THEN RETURN FALSE END;
    a := b; b := t; INC(i)
  END;
  r := b; RETURN TRUE
END Derangements;

PROCEDURE StirlingSecond (n, k: LONGCARD; VAR r: BigNat.T) : BOOLEAN;
(* S(n, k) = k S(n-1, k) + S(n-1, k-1); S(0, 0) = 1; row by row *)
CONST
  Max = 512;
VAR
  row: ARRAY [0..Max] OF BigNat.T;
  i, j: LONGCARD; t: BigNat.T;
BEGIN
  IF k > n THEN r.n := 0; RETURN TRUE END;
  IF n > Max THEN RETURN FALSE END;
  BigNat.FromNat(row[0], 1);
  j := 1; WHILE j <= k DO BigNat.FromNat(row[j], 0); INC(j) END;
  i := 1;
  WHILE i <= n DO
    j := k;
    IF i < j THEN j := i END;
    WHILE j >= 1 DO
      IF NOT BigNat.MulSmall(row[j], VAL(CARDINAL, j), t) THEN RETURN FALSE END;
      IF NOT BigNat.Add(t, row[j - 1], row[j]) THEN RETURN FALSE END;
      DEC(j)
    END;
    BigNat.FromNat(row[0], 0);
    INC(i)
  END;
  r := row[k]; RETURN TRUE
END StirlingSecond;

PROCEDURE BernoulliTable (n: LONGCARD; plus: BOOLEAN; VAR r: Rat.T) : BOOLEAN;
(* bernoulli' n = 1 - ∑_{k<n} (n choose k) / (n - k + 1) * bernoulli' k   (Mathlib's definition)
   bernoulli n = (-1)^n * bernoulli' n *)
CONST
  Max = 256;
VAR
  B: ARRAY [0..Max] OF Rat.T;
  m, k: LONGCARD; s, term, c: Rat.T; cb: BigNat.T; cz: BigInt.T;
BEGIN
  IF n > Max THEN RETURN FALSE END;
  Rat.FromNat(B[0], 1);
  m := 1;
  WHILE m <= n DO
    Rat.FromNat(s, 0);
    k := 0;
    WHILE k < m DO
      IF NOT ChooseBig(m, k, cb) THEN RETURN FALSE END;
      BigInt.OfBigNat(cb, cz);
      Rat.OfBigInt(cz, c);
      IF NOT Rat.MakeSmall(1, m - k + 1, term) THEN RETURN FALSE END;
      IF NOT Rat.Mul(c, term, term) THEN RETURN FALSE END;
      IF NOT Rat.Mul(term, B[k], term) THEN RETURN FALSE END;
      IF NOT Rat.Add(s, term, s) THEN RETURN FALSE END;
      INC(k)
    END;
    Rat.FromNat(term, 1);
    IF NOT Rat.Sub(term, s, B[m]) THEN RETURN FALSE END;
    INC(m)
  END;
  IF plus OR NOT ODD(n) THEN r := B[n] ELSE Rat.Neg(B[n], r) END;
  RETURN TRUE
END BernoulliTable;

PROCEDURE Bernoulli (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
BEGIN
  RETURN BernoulliTable(n, FALSE, r)
END Bernoulli;

PROCEDURE BernoulliPlus (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
BEGIN
  RETURN BernoulliTable(n, TRUE, r)
END BernoulliPlus;

PROCEDURE Harmonic (n: LONGCARD; VAR r: Rat.T) : BOOLEAN;
VAR
  s, t: Rat.T; i: LONGCARD;
BEGIN
  Rat.FromNat(s, 0); i := 1;
  WHILE i <= n DO
    IF NOT Rat.MakeSmall(1, i, t) THEN RETURN FALSE END;
    IF NOT Rat.Add(s, t, s) THEN RETURN FALSE END;
    INC(i)
  END;
  r := s; RETURN TRUE
END Harmonic;

END Combinatorics.
