(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE NumberTheory;

IMPORT NatArith;

PROCEDURE Gcd (a, b: LONGCARD) : LONGCARD;
VAR
  x, y, t: LONGCARD;
BEGIN
  x := a; y := b;
  WHILE y # 0 DO t := x MOD y; x := y; y := t END;
  RETURN x
END Gcd;

PROCEDURE Lcm (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF (a = 0) OR (b = 0) THEN r := 0; RETURN TRUE END;
  RETURN NatArith.Mul(a DIV Gcd(a, b), b, r)
END Lcm;

PROCEDURE Coprime (a, b: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Gcd(a, b) = 1
END Coprime;

PROCEDURE AddMod (a, b, m: LONGCARD) : LONGCARD;
VAR
  x, y: LONGCARD;
BEGIN
  x := a MOD m; y := b MOD m;
  IF x >= m - y THEN RETURN x - (m - y) END;
  RETURN x + y
END AddMod;

PROCEDURE MulMod (a, b, m: LONGCARD) : LONGCARD;
(* binary multiplication with modular additions: never forms a product above m *)
VAR
  r, x, y, q: LONGCARD;
BEGIN
  x := a MOD m; y := b MOD m;
  IF (x = 0) OR (y = 0) THEN RETURN 0 END;
  IF NatArith.Mul(x, y, q) THEN RETURN q MOD m END;
  r := 0;
  WHILE y # 0 DO
    IF ODD(y) THEN r := AddMod(r, x, m) END;
    x := AddMod(x, x, m);
    y := y DIV 2
  END;
  RETURN r
END MulMod;

PROCEDURE PowMod (a, e, m: LONGCARD) : LONGCARD;
VAR
  r, b, k: LONGCARD;
BEGIN
  IF m <= 1 THEN RETURN 0 END;
  r := 1; b := a MOD m; k := e;
  WHILE k # 0 DO
    IF ODD(k) THEN r := MulMod(r, b, m) END;
    b := MulMod(b, b, m);
    k := k DIV 2
  END;
  RETURN r
END PowMod;

PROCEDURE MinFac (n: LONGCARD) : LONGCARD;
VAR
  d: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 2 END;
  IF n = 1 THEN RETURN 1 END;
  IF NOT ODD(n) THEN RETURN 2 END;
  d := 3;
  WHILE d <= n DIV d DO
    IF n MOD d = 0 THEN RETURN d END;
    d := d + 2
  END;
  RETURN n
END MinFac;

PROCEDURE IsPrime (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN (n >= 2) AND (MinFac(n) = n)
END IsPrime;

PROCEDURE NextPrime (n: LONGCARD; VAR p: LONGCARD) : BOOLEAN;
VAR
  k: LONGCARD;
BEGIN
  IF n <= 2 THEN p := 2; RETURN TRUE END;
  k := n;
  LOOP
    IF IsPrime(k) THEN p := k; RETURN TRUE END;
    IF k = NatArith.MaxNat THEN RETURN FALSE END;
    INC(k)
  END
END NextPrime;

PROCEDURE NthPrime (k: LONGCARD; VAR p: LONGCARD) : BOOLEAN;
VAR
  c, q: LONGCARD;
BEGIN
  q := 2; c := 0;
  LOOP
    IF IsPrime(q) THEN
      IF c = k THEN p := q; RETURN TRUE END;
      INC(c)
    END;
    IF q = NatArith.MaxNat THEN RETURN FALSE END;
    INC(q)
  END
END NthPrime;

PROCEDURE PrimeCounting (n: LONGCARD) : LONGCARD;
VAR
  c, k: LONGCARD;
BEGIN
  c := 0; k := 2;
  WHILE k <= n DO
    IF IsPrime(k) THEN INC(c) END;
    IF k = NatArith.MaxNat THEN RETURN c END;
    INC(k)
  END;
  RETURN c
END PrimeCounting;

PROCEDURE PrimeCountingBelow (n: LONGCARD) : LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  RETURN PrimeCounting(n - 1)
END PrimeCountingBelow;

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

PROCEDURE Omega (n: LONGCARD) : LONGCARD;
VAR
  k, m, d: LONGCARD;
BEGIN
  IF n <= 1 THEN RETURN 0 END;
  k := 0; m := n; d := 2;
  WHILE d <= m DIV d DO
    IF m MOD d = 0 THEN
      INC(k);
      WHILE m MOD d = 0 DO m := m DIV d END
    END;
    INC(d)
  END;
  IF m > 1 THEN INC(k) END;
  RETURN k
END Omega;

PROCEDURE PrimeFactorNth (n, k: LONGCARD) : LONGCARD;
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
END PrimeFactorNth;

PROCEDURE MaxPrimeFac (n: LONGCARD) : LONGCARD;
VAR
  m, d, last: LONGCARD;
BEGIN
  IF n <= 1 THEN RETURN 0 END;
  m := n; d := 2; last := 0;
  WHILE d <= m DIV d DO
    WHILE m MOD d = 0 DO m := m DIV d; last := d END;
    INC(d)
  END;
  IF m > 1 THEN last := m END;
  RETURN last
END MaxPrimeFac;

PROCEDURE PadicValNat (p, n: LONGCARD) : LONGCARD;
VAR
  k, m: LONGCARD;
BEGIN
  IF (p <= 1) OR (n = 0) THEN RETURN 0 END;
  k := 0; m := n;
  WHILE m MOD p = 0 DO m := m DIV p; INC(k) END;
  RETURN k
END PadicValNat;

PROCEDURE Factorization (n, p: LONGCARD) : LONGCARD;
BEGIN
  IF NOT IsPrime(p) THEN RETURN 0 END;
  RETURN PadicValNat(p, n)
END Factorization;

PROCEDURE Radical (n: LONGCARD) : LONGCARD;
(* ∏ p over n.primeFactors; primeFactors 0 = ∅, so rad 0 = 1 (empty product) *)
VAR
  r, m, d: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 1 END;
  r := 1; m := n; d := 2;
  WHILE d <= m DIV d DO
    IF m MOD d = 0 THEN
      r := r * d;
      WHILE m MOD d = 0 DO m := m DIV d END
    END;
    INC(d)
  END;
  IF m > 1 THEN r := r * m END;
  RETURN r
END Radical;

PROCEDURE SquarefreePart (n: LONGCARD) : LONGCARD;
(* n.factorization.prod (fun p e => p ^ (e % 2)); factorization 0 = 0, so the part of 0 is 1 *)
VAR
  r, m, d, e: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 1 END;
  r := 1; m := n; d := 2;
  WHILE d <= m DIV d DO
    e := 0;
    WHILE m MOD d = 0 DO m := m DIV d; INC(e) END;
    IF ODD(e) THEN r := r * d END;
    INC(d)
  END;
  IF m > 1 THEN r := r * m END;
  RETURN r
END SquarefreePart;

PROCEDURE IsSquarefree (n: LONGCARD) : BOOLEAN;
VAR
  m, d: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN FALSE END;
  m := n; d := 2;
  WHILE d <= m DIV d DO
    IF m MOD d = 0 THEN
      m := m DIV d;
      IF m MOD d = 0 THEN RETURN FALSE END
    END;
    INC(d)
  END;
  RETURN TRUE
END IsSquarefree;

PROCEDURE IsPrimePow (n: LONGCARD) : BOOLEAN;
VAR
  p, m: LONGCARD;
BEGIN
  IF n < 2 THEN RETURN FALSE END;
  p := MinFac(n); m := n;
  WHILE m MOD p = 0 DO m := m DIV p END;
  RETURN m = 1
END IsPrimePow;

PROCEDURE IsPowerful (n: LONGCARD) : BOOLEAN;
(* Mathlib Nat.Powerful: ∀ p, p.Prime → p ∣ n → p^2 ∣ n (so 0 and 1 are powerful) *)
VAR
  m, d, e: LONGCARD;
BEGIN
  IF n <= 1 THEN RETURN TRUE END;
  m := n; d := 2;
  WHILE d <= m DIV d DO
    e := 0;
    WHILE m MOD d = 0 DO m := m DIV d; INC(e) END;
    IF e = 1 THEN RETURN FALSE END;
    INC(d)
  END;
  RETURN m = 1
END IsPowerful;

PROCEDURE DivisorCount (n: LONGCARD) : LONGCARD;
VAR
  r, m, d, e: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  r := 1; m := n; d := 2;
  WHILE d <= m DIV d DO
    e := 0;
    WHILE m MOD d = 0 DO m := m DIV d; INC(e) END;
    r := r * (e + 1);
    INC(d)
  END;
  IF m > 1 THEN r := r * 2 END;
  RETURN r
END DivisorCount;

PROCEDURE DivisorSigma (k, n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* multiplicative: σ_k(p^e) = 1 + p^k + … + p^(ek) *)
VAR
  acc, m, d, e, term, pk, s: LONGCARD;

  PROCEDURE PrimePart (p, ex: LONGCARD; VAR v: LONGCARD) : BOOLEAN;
  VAR
    i: LONGCARD;
  BEGIN
    IF NOT NatArith.Pow(p, k, pk) THEN RETURN FALSE END;
    s := 1; term := 1; i := 0;
    WHILE i < ex DO
      IF NOT NatArith.Mul(term, pk, term) THEN RETURN FALSE END;
      IF NOT NatArith.Add(s, term, s) THEN RETURN FALSE END;
      INC(i)
    END;
    v := s; RETURN TRUE
  END PrimePart;

VAR
  v: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  acc := 1; m := n; d := 2;
  WHILE d <= m DIV d DO
    e := 0;
    WHILE m MOD d = 0 DO m := m DIV d; INC(e) END;
    IF e > 0 THEN
      IF NOT PrimePart(d, e, v) THEN RETURN FALSE END;
      IF NOT NatArith.Mul(acc, v, acc) THEN RETURN FALSE END
    END;
    INC(d)
  END;
  IF m > 1 THEN
    IF NOT PrimePart(m, 1, v) THEN RETURN FALSE END;
    IF NOT NatArith.Mul(acc, v, acc) THEN RETURN FALSE END
  END;
  r := acc; RETURN TRUE
END DivisorSigma;

PROCEDURE ProperDivisorSum (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  s: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF NOT DivisorSigma(1, n, s) THEN RETURN FALSE END;
  r := s - n; RETURN TRUE
END ProperDivisorSum;

PROCEDURE IsPerfect (n: LONGCARD) : BOOLEAN;
VAR
  s: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN FALSE END;
  RETURN ProperDivisorSum(n, s) AND (s = n)
END IsPerfect;

PROCEDURE Totient (n: LONGCARD) : LONGCARD;
VAR
  r, m, d: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  r := n; m := n; d := 2;
  WHILE d <= m DIV d DO
    IF m MOD d = 0 THEN
      WHILE m MOD d = 0 DO m := m DIV d END;
      r := r - r DIV d
    END;
    INC(d)
  END;
  IF m > 1 THEN r := r - r DIV m END;
  RETURN r
END Totient;

PROCEDURE Moebius (n: LONGCARD) : INTEGER;
VAR
  m, d, e: LONGCARD; s: INTEGER;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  s := 1; m := n; d := 2;
  WHILE d <= m DIV d DO
    e := 0;
    WHILE m MOD d = 0 DO m := m DIV d; INC(e) END;
    IF e > 1 THEN RETURN 0 END;
    IF e = 1 THEN s := -s END;
    INC(d)
  END;
  IF m > 1 THEN s := -s END;
  RETURN s
END Moebius;

PROCEDURE UnitaryDivisorCount (n: LONGCARD) : LONGCARD;
VAR
  r: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  IF NOT NatArith.Pow(2, Omega(n), r) THEN RETURN 0 END;   (* ω(n) <= 15 for 64-bit n *)
  RETURN r
END UnitaryDivisorCount;

PROCEDURE ModLongint (a: LONGINT; m: LONGCARD) : LONGCARD;   (* a mod m in [0, m), m > 0 *)
VAR
  u: LONGCARD;
BEGIN
  IF a >= 0 THEN RETURN VAL(LONGCARD, a) MOD m END;
  u := (VAL(LONGCARD, -(a + 1)) + 1) MOD m;                  (* |a| mod m *)
  IF u = 0 THEN RETURN 0 END;
  RETURN m - u
END ModLongint;

PROCEDURE Legendre (a: LONGINT; p: LONGCARD) : INTEGER;
(* quadratic character of ZMod p at a: 0 if p ∣ a, else 1 / -1 by Euler's criterion;
   for p = 2 every unit is a square, so the value is a mod 2 *)
VAR
  r, t: LONGCARD;
BEGIN
  r := ModLongint(a, p);
  IF r = 0 THEN RETURN 0 END;
  IF p = 2 THEN RETURN 1 END;
  t := PowMod(r, (p - 1) DIV 2, p);
  IF t = 1 THEN RETURN 1 END;
  RETURN -1
END Legendre;

PROCEDURE Jacobi (a: LONGINT; b: LONGCARD) : INTEGER;
(* Mathlib: jacobiSym a b = ∏ p ∈ b.primeFactorsList, legendreSym p a; the empty product
   (b = 0 or b = 1) is 1 *)
VAR
  m, d: LONGCARD; s: INTEGER;
BEGIN
  s := 1; m := b; d := 2;
  IF b <= 1 THEN RETURN 1 END;
  WHILE d <= m DIV d DO
    WHILE m MOD d = 0 DO
      s := s * Legendre(a, d);
      m := m DIV d
    END;
    INC(d)
  END;
  IF m > 1 THEN s := s * Legendre(a, m) END;
  RETURN s
END Jacobi;

END NumberTheory.
