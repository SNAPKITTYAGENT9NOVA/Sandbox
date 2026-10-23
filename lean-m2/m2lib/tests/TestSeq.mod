(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE TestSeq;
(* NatSeq (List ℕ / Finset ℕ operations) and the A113254 property theorem
   `∀ n, IsSquare (a (2 n + 1))` from FormalConjectures/OEIS/113254.lean, checked for the
   indices whose value fits in 64 bits. Expected lists are written out by hand from the Lean
   definitions (List.range, Finset.Icc, Nat.divisors, Nat.primeFactorsList, …). *)

IMPORT Check, NatSeq, NatArith, OeisInt;

VAR
  a, b, c: NatSeq.T; s, m, n: LONGCARD; i: CARDINAL; v: LONGINT; ok: BOOLEAN;

PROCEDURE Even (x: LONGCARD) : BOOLEAN;
BEGIN
  RETURN x MOD 2 = 0
END Even;

PROCEDURE Big (x: LONGCARD) : BOOLEAN;
BEGIN
  RETURN x > 100
END Big;

PROCEDURE Sq (x: LONGCARD) : LONGCARD;
BEGIN
  RETURN x * x
END Sq;

PROCEDURE Mod3 (x: LONGCARD) : LONGCARD;
BEGIN
  RETURN x MOD 3
END Mod3;

PROCEDURE Is (name: ARRAY OF CHAR; VAR l: NatSeq.T; want: ARRAY OF LONGCARD; len: CARDINAL);
VAR i: CARDINAL; same: BOOLEAN;
BEGIN
  same := l.len = len; i := 0;
  WHILE same AND (i < len) DO
    IF l.x[i] # want[i] THEN same := FALSE END;
    INC(i)
  END;
  Check.True(name, same)
END Is;

PROCEDURE L3 (x0, x1, x2: LONGCARD; VAR l: NatSeq.T);
BEGIN
  l.len := 3; l.x[0] := x0; l.x[1] := x1; l.x[2] := x2
END L3;

VAR
  w: ARRAY [0..15] OF LONGCARD;

BEGIN
  (* construction *)
  ok := NatSeq.Range(0, a); Check.True("Range 0 = []", ok AND (a.len = 0));
  ok := NatSeq.Range(5, a);
  w[0] := 0; w[1] := 1; w[2] := 2; w[3] := 3; w[4] := 4; Is("Range 5", a, w, 5);
  ok := NatSeq.Icc(3, 3, a); w[0] := 3; Is("Icc 3 3", a, w, 1);
  ok := NatSeq.Icc(4, 3, a); Check.True("Icc 4 3 = []", ok AND (a.len = 0));
  ok := NatSeq.Ico(2, 5, a); w[0] := 2; w[1] := 3; w[2] := 4; Is("Ico 2 5", a, w, 3);
  ok := NatSeq.Ioc(2, 5, a); w[0] := 3; w[1] := 4; w[2] := 5; Is("Ioc 2 5", a, w, 3);
  ok := NatSeq.Ico(5, 5, a); Check.True("Ico 5 5 = []", ok AND (a.len = 0));
  ok := NatSeq.Range(4097, a); Check.Fails("Range 4097 (capacity)", 4097, ok);
  ok := NatSeq.Icc(18446744073709551614, 18446744073709551615, a);
  Check.True("Icc at 2^64 - 1", ok AND (a.len = 2) AND (a.x[1] = 18446744073709551615));

  (* access with defaults *)
  ok := NatSeq.Range(5, a);
  Check.Nat("Get 4", 4, TRUE, NatSeq.Get(a, 4), 4);
  Check.Nat("Get 5 (getD 0)", 5, TRUE, NatSeq.Get(a, 5), 0);
  Check.Nat("Head", 0, TRUE, NatSeq.Head(a, 99), 0);
  Check.Nat("Last", 0, TRUE, NatSeq.Last(a, 99), 4);
  NatSeq.Clear(b);
  Check.Nat("Head [] (headD)", 0, TRUE, NatSeq.Head(b, 99), 99);
  Check.Nat("Last [] (getLastD)", 0, TRUE, NatSeq.Last(b, 7), 7);

  (* filter / map / folds *)
  ok := NatSeq.Range(10, a);
  NatSeq.Filter(a, Even, b); w[0] := 0; w[1] := 2; w[2] := 4; w[3] := 6; w[4] := 8; Is("Filter even", b, w, 5);
  NatSeq.Filter(a, Big, b); Check.True("Filter none", b.len = 0);
  NatSeq.Map(a, Sq, b); Check.Nat("Map sq [9]", 9, TRUE, b.x[9], 81);
  ok := NatSeq.Sum(b, s); Check.Nat("Sum squares < 10", 0, ok, s, 285);
  ok := NatSeq.Prod(a, s); Check.Nat("Prod with 0", 0, ok, s, 0);
  ok := NatSeq.Icc(1, 20, a); ok := NatSeq.Prod(a, s); Check.Nat("Prod 1..20 = 20!", 20, ok, s, 2432902008176640000);
  ok := NatSeq.Icc(1, 21, a); ok := NatSeq.Prod(a, s); Check.Fails("Prod 1..21 overflows", 21, ok);
  ok := NatSeq.Icc(0, 21, a); ok := NatSeq.Prod(a, s); Check.Nat("Prod 0..21 = 0", 21, ok, s, 0);
  NatSeq.Clear(a); ok := NatSeq.Prod(a, s); Check.Nat("Prod [] = 1", 0, ok, s, 1);
  ok := NatSeq.Sum(a, s); Check.Nat("Sum [] = 0", 0, ok, s, 0);
  a.len := 2; a.x[0] := 18446744073709551615; a.x[1] := 1;
  ok := NatSeq.Sum(a, s); Check.Fails("Sum overflow", 0, ok);
  ok := NatSeq.Range(10, a);
  Check.Nat("CountP even", 0, TRUE, NatSeq.CountP(a, Even), 5);
  Check.True("All even (false)", NOT NatSeq.All(a, Even));
  Check.True("Any even", NatSeq.Any(a, Even));
  NatSeq.Clear(b);
  Check.True("All [] = true", NatSeq.All(b, Big));
  Check.True("Any [] = false", NOT NatSeq.Any(b, Even));
  Check.Nat("IndexOf 7", 7, TRUE, NatSeq.IndexOf(a, 7), 7);
  Check.Nat("IndexOf absent = length", 70, TRUE, NatSeq.IndexOf(a, 70), 10);
  Check.Nat("Sup", 0, TRUE, NatSeq.Sup(a), 9);
  Check.Nat("Sup [] = 0", 0, TRUE, NatSeq.Sup(b), 0);
  ok := NatSeq.Inf(a, m); Check.Nat("Inf", 0, ok, m, 0);
  ok := NatSeq.Inf(b, m); Check.Fails("Inf []", 0, ok);

  (* reverse / take / drop / append *)
  L3(1, 2, 3, a);
  NatSeq.Reverse(a, b); w[0] := 3; w[1] := 2; w[2] := 1; Is("Reverse", b, w, 3);
  NatSeq.Reverse(a, a); Is("Reverse in place", a, w, 3);
  NatSeq.Take(a, 2, b); Is("Take 2", b, w, 2);
  NatSeq.Take(a, 9, b); Is("Take 9", b, w, 3);
  NatSeq.Drop(a, 1, b); w[0] := 2; w[1] := 1; Is("Drop 1", b, w, 2);
  NatSeq.Drop(a, 5, b); Check.True("Drop 5 = []", b.len = 0);
  L3(1, 2, 3, a); L3(4, 5, 6, b);
  ok := NatSeq.Append(a, b, c); w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 4; w[4] := 5; w[5] := 6; Is("Append", c, w, 6);
  ok := NatSeq.Append(a, b, b); Is("Append aliasing b", b, w, 6);

  (* sort / dedup / finsets *)
  a.len := 8; a.x[0] := 5; a.x[1] := 3; a.x[2] := 5; a.x[3] := 1; a.x[4] := 9; a.x[5] := 3; a.x[6] := 0; a.x[7] := 5;
  Check.True("Nodup false", NOT NatSeq.Nodup(a));
  Check.Nat("Count 5", 5, TRUE, NatSeq.Count(a, 5), 3);
  b := a; NatSeq.Dedup(b); w[0] := 5; w[1] := 3; w[2] := 1; w[3] := 9; w[4] := 0; Is("Dedup keeps first", b, w, 5);
  Check.True("Nodup after Dedup", NatSeq.Nodup(b));
  b := a; NatSeq.Sort(b); w[0] := 0; w[1] := 1; w[2] := 3; w[3] := 3; w[4] := 5; w[5] := 5; w[6] := 5; w[7] := 9;
  Is("Sort", b, w, 8);
  Check.True("IsSorted", NatSeq.IsSorted(b) AND NOT NatSeq.IsSorted(a));
  NatSeq.ToFinset(a); w[0] := 0; w[1] := 1; w[2] := 3; w[3] := 5; w[4] := 9; Is("ToFinset", a, w, 5);
  Check.True("FinsetMem 5", NatSeq.FinsetMem(a, 5));
  Check.True("FinsetMem 4", NOT NatSeq.FinsetMem(a, 4));
  L3(1, 4, 9, b);
  ok := NatSeq.Union(a, b, c); w[0] := 0; w[1] := 1; w[2] := 3; w[3] := 4; w[4] := 5; w[5] := 9; Is("Union", c, w, 6);
  NatSeq.Inter(a, b, c); w[0] := 1; w[1] := 9; Is("Inter", c, w, 2);
  NatSeq.Diff(a, b, c); w[0] := 0; w[1] := 3; w[2] := 5; Is("Diff", c, w, 3);
  NatSeq.Diff(b, a, c); w[0] := 4; Is("Diff reversed", c, w, 1);
  NatSeq.Inter(a, b, c);
  Check.True("Subset", NatSeq.Subset(c, a) AND NatSeq.Subset(c, b) AND NOT NatSeq.Subset(b, a));
  ok := NatSeq.Range(10, a); NatSeq.Image(a, Mod3, b); w[0] := 0; w[1] := 1; w[2] := 2; Is("Image mod 3", b, w, 3);
  (* a large sort *)
  a.len := NatSeq.MaxLen; FOR i := 0 TO NatSeq.MaxLen - 1 DO a.x[i] := (VAL(LONGCARD, i) * 2654435761) MOD 1000 END;
  NatSeq.Sort(a); Check.True("Sort 4096", NatSeq.IsSorted(a) AND (a.len = NatSeq.MaxLen));

  (* number-theoretic lists *)
  ok := NatSeq.Divisors(0, a); Check.True("divisors 0 = ∅", ok AND (a.len = 0));
  ok := NatSeq.Divisors(1, a); w[0] := 1; Is("divisors 1", a, w, 1);
  ok := NatSeq.Divisors(36, a);
  w[0] := 1; w[1] := 2; w[2] := 3; w[3] := 4; w[4] := 6; w[5] := 9; w[6] := 12; w[7] := 18; w[8] := 36;
  Is("divisors 36", a, w, 9);
  ok := NatSeq.ProperDivisors(36, a); Is("properDivisors 36", a, w, 8);
  ok := NatSeq.ProperDivisors(1, a); Check.True("properDivisors 1 = ∅", ok AND (a.len = 0));
  ok := NatSeq.Divisors(735134400, a); Check.True("divisors 735134400 has 1344", ok AND (a.len = 1344));
  ok := NatSeq.PrimeFactorsList(360, a);
  w[0] := 2; w[1] := 2; w[2] := 2; w[3] := 3; w[4] := 3; w[5] := 5; Is("primeFactorsList 360", a, w, 6);
  ok := NatSeq.PrimeFactorsList(0, a); Check.True("primeFactorsList 0 = []", ok AND (a.len = 0));
  ok := NatSeq.PrimeFactorsList(1, a); Check.True("primeFactorsList 1 = []", ok AND (a.len = 0));
  ok := NatSeq.PrimeFactors(360, a); w[0] := 2; w[1] := 3; w[2] := 5; Is("primeFactors 360", a, w, 3);
  ok := NatSeq.PrimesBelow(30, a);
  w[0] := 2; w[1] := 3; w[2] := 5; w[3] := 7; w[4] := 11; w[5] := 13; w[6] := 17; w[7] := 19; w[8] := 23; w[9] := 29;
  Is("primesBelow 30", a, w, 10);
  ok := NatSeq.PrimesBelow(2, a); Check.True("primesBelow 2 = ∅", ok AND (a.len = 0));
  ok := NatSeq.PrimesBelow(38000, a); Check.True("primesBelow 38000 has 4017", ok AND (a.len = 4017));
  ok := NatSeq.PrimesBelow(40000, a); Check.Fails("primesBelow 40000 (4203 > capacity)", 40000, ok);

  (* A113254: ∀ n, IsSquare (a (2 n + 1)) *)
  n := 0;
  LOOP
    ok := OeisInt.A113254(2 * n + 1, v);
    IF NOT ok THEN EXIT END;
    Check.True("A113254 a(2n+1) square", (v >= 0) AND NatArith.IsSquare(VAL(LONGCARD, v)));
    INC(n)
  END;
  Check.True("A113254 checked at least 5 odd indices", n >= 5);

  Check.Done("TestSeq")
END TestSeq.
