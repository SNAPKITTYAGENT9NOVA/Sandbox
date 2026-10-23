(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE NatSearch;

IMPORT NatSeq, NatArith, NumberTheory, ModArith, Digits;

VAR
  divs: NatSeq.T;
  reach: ARRAY [0..1048576] OF BOOLEAN;      (* subset-sum table for Pseudoperfect / Practical *)

PROCEDURE Count (p: Pred; n: LONGCARD) : LONGCARD;
VAR m, c: LONGCARD;
BEGIN
  c := 0; m := 0;
  WHILE m < n DO
    IF p(m) THEN INC(c) END;
    INC(m)
  END;
  RETURN c
END Count;

PROCEDURE CountIcc (p: Pred; a, b: LONGCARD) : LONGCARD;
VAR m, c: LONGCARD;
BEGIN
  IF a > b THEN RETURN 0 END;
  c := 0; m := a;
  LOOP
    IF p(m) THEN INC(c) END;
    IF m = b THEN EXIT END;
    INC(m)
  END;
  RETURN c
END CountIcc;

PROCEDURE FindFrom (p: Pred; lo, limit: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR m: LONGCARD;
BEGIN
  IF lo > limit THEN RETURN FALSE END;
  m := lo;
  LOOP
    IF p(m) THEN r := m; RETURN TRUE END;
    IF m = limit THEN RETURN FALSE END;
    INC(m)
  END
END FindFrom;

PROCEDURE Find (p: Pred; limit: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  RETURN FindFrom(p, 0, limit, r)
END Find;

PROCEDURE Nth (p: Pred; k, limit: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR m, c: LONGCARD;
BEGIN
  c := 0; m := 0;
  LOOP
    IF p(m) THEN
      IF c = k THEN r := m; RETURN TRUE END;
      INC(c)
    END;
    IF m = limit THEN RETURN FALSE END;
    INC(m)
  END
END Nth;

PROCEDURE GreatestBelow (p: Pred; n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR m: LONGCARD;
BEGIN
  m := n;
  WHILE m > 0 DO
    DEC(m);
    IF p(m) THEN r := m; RETURN TRUE END
  END;
  RETURN FALSE
END GreatestBelow;

PROCEDURE Prime (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN ModArith.IsPrime(n)
END Prime;

PROCEDURE Composite (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN (n > 1) AND NOT ModArith.IsPrime(n)
END Composite;

PROCEDURE Squarefree (n: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored; i: CARDINAL;
BEGIN
  IF n = 0 THEN RETURN FALSE END;
  ModArith.Factor(n, f);
  i := 0;
  WHILE i < f.count DO
    IF f.e[i] > 1 THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Squarefree;

PROCEDURE Powerful (n: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored; i: CARDINAL;
BEGIN
  IF n = 0 THEN RETURN TRUE END;
  ModArith.Factor(n, f);
  i := 0;
  WHILE i < f.count DO
    IF f.e[i] < 2 THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Powerful;

PROCEDURE Square (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NatArith.IsSquare(n)
END Square;

PROCEDURE PrimePow (n: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored;
BEGIN
  IF n < 2 THEN RETURN FALSE END;
  ModArith.Factor(n, f);
  RETURN f.count = 1
END PrimePow;

PROCEDURE Even (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NOT ODD(n)
END Even;

PROCEDURE Odd (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN ODD(n)
END Odd;

PROCEDURE ProperSum (n: LONGCARD; VAR s: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NumberTheory.ProperDivisorSum(n, s)
END ProperSum;

PROCEDURE Perfect (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NumberTheory.IsPerfect(n)
END Perfect;

PROCEDURE Abundant (n: LONGCARD) : BOOLEAN;
VAR s: LONGCARD;
BEGIN
  IF NOT ProperSum(n, s) THEN RETURN TRUE END;          (* the sum exceeds 2^64 - 1 > n *)
  RETURN n < s
END Abundant;

PROCEDURE Deficient (n: LONGCARD) : BOOLEAN;
VAR s: LONGCARD;
BEGIN
  IF NOT ProperSum(n, s) THEN RETURN FALSE END;
  RETURN s < n
END Deficient;

PROCEDURE SubsetSums (n: LONGCARD; target: CARDINAL);
(* reach[t] := t is a sum of distinct elements of divs (target ≥ every t considered) *)
VAR i, t: CARDINAL; d: LONGCARD;
BEGIN
  FOR t := 0 TO target DO reach[t] := FALSE END;
  reach[0] := TRUE;
  i := 0;
  WHILE i < divs.len DO
    d := divs.x[i];
    IF d <= VAL(LONGCARD, target) THEN
      t := target;
      WHILE t >= VAL(CARDINAL, d) DO
        IF reach[t - VAL(CARDINAL, d)] THEN reach[t] := TRUE END;
        DEC(t)
      END
    END;
    INC(i)
  END
END SubsetSums;

PROCEDURE Pseudoperfect (n: LONGCARD) : BOOLEAN;
BEGIN
  IF (n = 0) OR (n > 1048576) THEN RETURN FALSE END;
  IF NOT NatSeq.ProperDivisors(n, divs) THEN RETURN FALSE END;
  SubsetSums(n, VAL(CARDINAL, n));
  RETURN reach[VAL(CARDINAL, n)]
END Pseudoperfect;

PROCEDURE Weird (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Abundant(n) AND (n <= 1048576) AND NOT Pseudoperfect(n)
END Weird;

PROCEDURE TriLE (k, n: LONGCARD) : BOOLEAN;
(* k (k+1) / 2 <= n, decided without overflow: a product above 2^64 - 1 exceeds n *)
VAR t: LONGCARD;
BEGIN
  IF ODD(k) THEN
    IF NOT NatArith.Mul(k, k DIV 2 + 1, t) THEN RETURN FALSE END
  ELSE
    IF (k = MAX(LONGCARD)) OR NOT NatArith.Mul(k DIV 2, k + 1, t) THEN RETURN FALSE END
  END;
  RETURN t <= n
END TriLE;

PROCEDURE Triangular (n: LONGCARD) : BOOLEAN;
(* the k with T(k) <= n < T(k+1) lies near √(2n) = 2 √(n/2); n is triangular iff T(k) = n,
   i.e. iff T(k) <= n and NOT T(k) <= n - 1 *)
VAR k: LONGCARD;
BEGIN
  k := 2 * NatArith.Sqrt(n DIV 2);
  WHILE (k > 0) AND NOT TriLE(k, n) DO DEC(k) END;
  WHILE TriLE(k + 1, n) DO INC(k) END;
  RETURN (n = 0) OR NOT TriLE(k, n - 1)
END Triangular;

PROCEDURE Palindrome10 (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Digits.IsPalindrome(10, n)
END Palindrome10;

PROCEDURE Refactorable (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN (n > 0) AND (n MOD NumberTheory.DivisorCount(n) = 0)
END Refactorable;

PROCEDURE TwinPrime (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN (n <= MAX(LONGCARD) - 2) AND Prime(n) AND Prime(n + 2)
END TwinPrime;

PROCEDURE SophieGermain (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN (n < 9223372036854775807) AND Prime(n) AND Prime(2 * n + 1)
END SophieGermain;

PROCEDURE Practical (n: LONGCARD) : BOOLEAN;
VAR t: CARDINAL;
BEGIN
  IF (n = 0) OR (n > 1048576) THEN RETURN FALSE END;
  IF NOT NatSeq.Divisors(n, divs) THEN RETURN FALSE END;
  SubsetSums(n, VAL(CARDINAL, n));
  FOR t := 1 TO VAL(CARDINAL, n) DO
    IF NOT reach[t] THEN RETURN FALSE END
  END;
  RETURN TRUE
END Practical;

PROCEDURE Carmichael (n: LONGCARD) : BOOLEAN;
(* Korselt: n composite, squarefree, and p - 1 ∣ n - 1 for every prime p ∣ n — equivalent to
   a^(n-1) ≡ 1 (mod n) for all a coprime to n *)
VAR f: ModArith.Factored; i: CARDINAL;
BEGIN
  IF (n < 3) OR ModArith.IsPrime(n) THEN RETURN FALSE END;
  ModArith.Factor(n, f);
  i := 0;
  WHILE i < f.count DO
    IF (f.e[i] > 1) OR ((n - 1) MOD (f.p[i] - 1) # 0) THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Carmichael;

END NatSearch.
