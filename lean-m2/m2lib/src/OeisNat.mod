(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE OeisNat;

IMPORT NatArith, NumberTheory, Combinatorics, Digits, NatSeq, ModArith, BigNat;
FROM NatArith IMPORT Sub;

CONST
  MemoMax = 1048576;                       (* 2^20 *)

VAR
  memo: ARRAY [0..MemoMax] OF LONGCARD;
  mark: ARRAY [0..MemoMax] OF BOOLEAN;
  kol: ARRAY [0..16010] OF CARDINAL;
  setA, setB, setC: NatSeq.T;

(* ---- checked arithmetic: on overflow, ok becomes FALSE and the result is 0 ---- *)

PROCEDURE Ad (a, b: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR r: LONGCARD;
BEGIN
  IF NOT NatArith.Add(a, b, r) THEN ok := FALSE; RETURN 0 END;
  RETURN r
END Ad;

PROCEDURE Mu (a, b: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR r: LONGCARD;
BEGIN
  IF NOT NatArith.Mul(a, b, r) THEN ok := FALSE; RETURN 0 END;
  RETURN r
END Mu;

PROCEDURE Pw (a, e: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR r: LONGCARD;
BEGIN
  IF NOT NatArith.Pow(a, e, r) THEN ok := FALSE; RETURN 0 END;
  RETURN r
END Pw;

PROCEDURE Ch (n, k: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR r: LONGCARD;
BEGIN
  IF NOT Combinatorics.Choose(n, k, r) THEN ok := FALSE; RETURN 0 END;
  RETURN r
END Ch;

PROCEDURE Fa (n: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR r: LONGCARD;
BEGIN
  IF NOT Combinatorics.Factorial(n, r) THEN ok := FALSE; RETURN 0 END;
  RETURN r
END Fa;

PROCEDURE Prime (n: LONGCARD) : BOOLEAN;
BEGIN
  RETURN ModArith.IsPrime(n)
END Prime;

PROCEDURE Pw2 (k: LONGCARD) : LONGCARD;           (* 2^k for k < 64 *)
VAR r: LONGCARD;
BEGIN
  r := 1;
  WHILE k > 0 DO r := r * 2; DEC(k) END;
  RETURN r
END Pw2;

PROCEDURE CountPrimesBelow (x: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* #{p < x : p prime} by a sieve over mark[0 .. x-1]; x <= 2^20 *)
VAR i, j, m: CARDINAL; c: LONGCARD;
BEGIN
  IF x > MemoMax THEN RETURN FALSE END;
  r := 0;
  IF x <= 2 THEN RETURN TRUE END;
  m := VAL(CARDINAL, x);
  FOR i := 0 TO m - 1 DO mark[i] := TRUE END;
  mark[0] := FALSE; mark[1] := FALSE;
  i := 2;
  WHILE i * i < m DO
    IF mark[i] THEN
      j := i * i;
      WHILE j < m DO mark[j] := FALSE; INC(j, i) END
    END;
    INC(i)
  END;
  c := 0;
  FOR i := 2 TO m - 1 DO IF mark[i] THEN INC(c) END END;
  r := c;
  RETURN TRUE
END CountPrimesBelow;

(* ---------------------------------------------------------------------------------- *)

PROCEDURE A000002 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR len, i, m, run, sym, k: CARDINAL;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF n > 8000 THEN RETURN FALSE END;
  m := VAL(CARDINAL, n - 1);                         (* a (m + 1) = (wordPrefix m).getD m 0 *)
  kol[0] := 1; kol[1] := 2; kol[2] := 2; len := 3;
  i := 0;
  WHILE i < m DO
    IF (i + 2 < len) AND (kol[i + 2] = 2) THEN run := 2 ELSE run := 1 END;
    IF i MOD 2 = 0 THEN sym := 1 ELSE sym := 2 END;
    FOR k := 1 TO run DO kol[len] := sym; INC(len) END;
    INC(i)
  END;
  IF m < len THEN r := VAL(LONGCARD, kol[m]) ELSE r := 0 END;
  RETURN TRUE
END A000002;

PROCEDURE A000041 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR b: BigNat.T;
BEGIN
  IF NOT Combinatorics.Partitions(n, b) THEN RETURN FALSE END;
  RETURN BigNat.ToNat(b, r)
END A000041;

PROCEDURE A000224 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k, c: LONGCARD; i: CARDINAL; v: CARDINAL;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  IF n > MemoMax THEN RETURN FALSE END;
  FOR i := 0 TO VAL(CARDINAL, n) - 1 DO mark[i] := FALSE END;
  c := 0; k := 0;
  WHILE k < n DO
    v := VAL(CARDINAL, NumberTheory.MulMod(k, k, n));
    IF NOT mark[v] THEN mark[v] := TRUE; INC(c) END;
    INC(k)
  END;
  r := c; RETURN TRUE
END A000224;

PROCEDURE A000945 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR b, i: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  ok := TRUE; b := 1; i := 1;
  WHILE ok AND (i < n) DO                             (* b i = b (i-1) * minFac (b (i-1) + 1) *)
    b := Mu(b, ModArith.MinFacFast(Ad(b, 1, ok)), ok);
    INC(i)
  END;
  IF ok THEN r := ModArith.MinFacFast(Ad(b, 1, ok)) END;
  RETURN ok
END A000945;

PROCEDURE A001146 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR ok: BOOLEAN;
BEGIN
  ok := TRUE; r := Pw(2, Pw(2, n, ok), ok);
  RETURN ok
END A001146;

PROCEDURE A001157 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NumberTheory.DivisorSigma(2, n, r)
END A001157;

PROCEDURE A001818 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR p, k: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; p := 1; k := 0;
  WHILE ok AND (k < n) DO p := Mu(p, Ad(Mu(2, k, ok), 1, ok), ok); INC(k) END;
  r := Mu(p, p, ok);
  RETURN ok
END A001818;

PROCEDURE A002426 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n DIV 2) DO
    s := Ad(s, Mu(Ch(n, 2 * k, ok), Ch(2 * k, k, ok), ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A002426;

PROCEDURE A002454 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR f: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; f := Fa(n, ok);
  r := Mu(Pw(4, n, ok), Mu(f, f, ok), ok);
  RETURN ok
END A002454;

PROCEDURE A003161 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* ∑_{k ≤ n/2} (diff^3).toNat, diff = C(n,k) - [k > 0] C(n,k-1) in ℤ *)
VAR s, k, c1, c0, d: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n DIV 2) DO
    c1 := Ch(n, k, ok);
    IF k = 0 THEN c0 := 0 ELSE c0 := Ch(n, k - 1, ok) END;
    IF c1 >= c0 THEN                                 (* a negative cube contributes toNat = 0 *)
      d := c1 - c0;
      s := Ad(s, Pw(d, 3, ok), ok)
    END;
    INC(k)
  END;
  r := s; RETURN ok
END A003161;

PROCEDURE A005258 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k, c: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n) DO
    c := Ch(n, k, ok);
    s := Ad(s, Mu(Mu(c, c, ok), Ch(n + k, k, ok), ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A005258;

PROCEDURE A007013 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; a := 2; i := 0;
  WHILE ok AND (i < n) DO a := Sub(Pw(2, a, ok), 1); INC(i) END;
  r := a; RETURN ok
END A007013;

PROCEDURE A017666 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s: LONGCARD;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  IF NOT NumberTheory.DivisorSigma(1, n, s) THEN RETURN FALSE END;
  r := n DIV NumberTheory.Gcd(n, s);
  RETURN TRUE
END A017666;

PROCEDURE A022030 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 4; RETURN TRUE END;
  ok := TRUE; a0 := 4; a1 := 16; m := 2;
  WHILE ok AND (m <= n) DO
    IF (m - 2) MOD 2 = 0 THEN
      a2 := Sub(NatArith.Div(Sub(Ad(Mu(a1, a1, ok), a0, ok), 1), a0), 1)
    ELSE
      a2 := Ad(NatArith.Div(Mu(a1, a1, ok), a0), 1, ok)
    END;
    a0 := a1; a1 := a2; INC(m)
  END;
  r := a1; RETURN ok
END A022030;

PROCEDURE A038098 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR ok: BOOLEAN; x: LONGCARD;
BEGIN
  ok := TRUE; x := Pw(n, 3, ok);
  RETURN ok AND CountPrimesBelow(x, r)
END A038098;

PROCEDURE A038107 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR ok: BOOLEAN; x: LONGCARD;
BEGIN
  ok := TRUE; x := Pw(n, 2, ok);
  RETURN ok AND CountPrimesBelow(x, r)
END A038107;

PROCEDURE A048153 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0;
  IF n > 0 THEN
    k := 1;
    WHILE ok AND (k <= n) DO s := Ad(s, NumberTheory.MulMod(k, k, n), ok); INC(k) END
  END;
  r := s; RETURN ok
END A048153;

PROCEDURE A051903 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored; i: CARDINAL;
BEGIN
  r := 0;
  ModArith.Factor(n, f);                              (* count = 0 for n ≤ 1 *)
  i := 0;
  WHILE i < f.count DO
    IF VAL(LONGCARD, f.e[i]) > r THEN r := VAL(LONGCARD, f.e[i]) END;
    INC(i)
  END;
  RETURN TRUE
END A051903;

PROCEDURE A052709 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k < n) DO
    s := Ad(s, Mu(Ch(2 * k, k, ok) DIV (k + 1), Ch(k, Sub(Sub(n, 1), k), ok), ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A052709;

PROCEDURE Tri (n: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;   (* n (n+1) / 2 *)
BEGIN
  IF NOT ODD(n) THEN RETURN Mu(n DIV 2, Ad(n, 1, ok), ok) END;
  RETURN Mu(n, Ad(n, 1, ok) DIV 2, ok)
END Tri;

PROCEDURE A053067 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR v, hi, acc: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  ok := TRUE;
  v := Ad(Tri(n - 1, ok), 1, ok); hi := Tri(n, ok); acc := 0;
  WHILE ok AND (v <= hi) DO
    IF NOT Digits.Concat(acc, v, acc) THEN ok := FALSE END;
    INC(v)
  END;
  r := acc; RETURN ok
END A053067;

PROCEDURE A060957 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k: LONGCARD; i: CARDINAL; ok: BOOLEAN;
BEGIN
  NatSeq.Clear(setA);
  IF NOT NatSeq.Push(setA, 1) THEN RETURN FALSE END;
  ok := TRUE; k := 1;
  WHILE ok AND (k <= n) DO
    setB.len := setA.len; i := 0;
    WHILE i < setA.len DO setB.x[i] := Mu(setA.x[i], k, ok); INC(i) END;
    NatSeq.ToFinset(setB);
    IF ok AND NOT NatSeq.Union(setA, setB, setC) THEN ok := FALSE END;
    setA := setC;
    INC(k)
  END;
  r := VAL(LONGCARD, setA.len); RETURN ok
END A060957;

PROCEDURE A067599 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored; i: CARDINAL; acc: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n < 2 THEN r := 0; RETURN TRUE END;
  ModArith.Factor(n, f);
  ok := TRUE; acc := 0; i := 0;
  WHILE ok AND (i < f.count) DO
    ok := Digits.Concat(acc, f.p[i], acc) AND Digits.Concat(acc, VAL(LONGCARD, f.e[i]), acc);
    INC(i)
  END;
  r := acc; RETURN ok
END A067599;

PROCEDURE A067836 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR term, prod, q, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; term := 1; prod := 1; i := 0;
  WHILE ok AND (i < n) DO
    q := Ad(prod, 2, ok);                    (* least prime in [prod + 2, 2 (prod + 2)] *)
    WHILE ok AND NOT Prime(q) DO q := Ad(q, 1, ok) END;
    term := q - prod;
    prod := Mu(prod, term, ok);
    INC(i)
  END;
  r := term; RETURN ok
END A067836;

PROCEDURE A069004 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, c, n2: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; c := 0; s := 1; n2 := Mu(n, n, ok);
  WHILE ok AND (s < n) DO
    IF Prime(Ad(n2, Mu(s, s, ok), ok)) AND ok THEN INC(c) END;
    INC(s)
  END;
  r := c; RETURN ok
END A069004;

PROCEDURE A069922 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR lo, hi, x, c: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE;
  lo := Pw(n, n, ok); hi := Ad(lo, Mu(n, n, ok), ok);
  IF NOT ok THEN RETURN FALSE END;
  c := 0; x := lo;
  LOOP                                   (* [lo, hi]; stepping past hi could wrap at 2^64 - 1 *)
    IF Prime(x) THEN INC(c) END;
    IF x = hi THEN EXIT END;
    INC(x)
  END;
  r := c; RETURN TRUE
END A069922;

PROCEDURE Cat70823 (x, y: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
(* x * 10^(numDigitsBase10 y) + y, with numDigitsBase10 0 = 1 *)
VAR d: LONGCARD;
BEGIN
  IF y = 0 THEN d := 1 ELSE d := NatArith.Log(10, y) + 1 END;
  RETURN Ad(Mu(x, Pw(10, d, ok), ok), y, ok)
END Cat70823;

PROCEDURE A070823 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, a3, m, c1, c2: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n <= 1 THEN r := 0; RETURN TRUE END;
  ok := TRUE; a0 := 0; a1 := 0; a2 := 1; m := 3;
  WHILE ok AND (m <= n) DO
    c1 := Cat70823(a2, a1, ok); c2 := Cat70823(a1, a2, ok);
    a3 := NatArith.Dist(c1, c2);
    a0 := a1; a1 := a2; a2 := a3; INC(m)
  END;
  r := a2; RETURN ok
END A070823;

PROCEDURE A076141 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR pat, tgt: Digits.List; sq: LONGCARD; i, j, lp, lt: CARDINAL; c: LONGCARD; match: BOOLEAN;
BEGIN
  IF NOT NatArith.Mul(n, n, sq) THEN RETURN FALSE END;
  Digits.Bits(n, pat); Digits.Bits(sq, tgt);     (* least significant first *)
  IF pat.len = 0 THEN pat.len := 1; pat.d[0] := 0 END;    (* binaryPattern 0 = [0] *)
  IF tgt.len = 0 THEN tgt.len := 1; tgt.d[0] := 0 END;
  lp := pat.len; lt := tgt.len;
  (* most-significant-first position i corresponds to index lt - 1 - i *)
  c := 0; i := 0;
  WHILE i + lp <= lt DO
    match := TRUE; j := 0;
    WHILE match AND (j < lp) DO
      IF tgt.d[lt - 1 - (i + j)] # pat.d[lp - 1 - j] THEN match := FALSE END;
      INC(j)
    END;
    IF match THEN INC(c) END;
    INC(i)
  END;
  r := c; RETURN TRUE
END A076141;

PROCEDURE A077408 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, rv, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; a := 103; i := 0;
  WHILE ok AND (i < n) DO
    IF NOT Digits.Reverse(3, a, rv) THEN ok := FALSE END;
    a := Ad(a, rv, ok); INC(i)
  END;
  r := a; RETURN ok
END A077408;

PROCEDURE A078590 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a1, a2, a3, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF n <= 2 THEN r := 1; RETURN TRUE END;
  ok := TRUE; a1 := 1; a2 := 1; m := 3;
  WHILE ok AND (m <= n) DO
    a3 := NatArith.Div(Ad(Pw(2, a2, ok), 1, ok), a1);
    a1 := a2; a2 := a3; INC(m)
  END;
  r := a2; RETURN ok
END A078590;

PROCEDURE A089026 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF Prime(n) THEN r := n ELSE r := 1 END;
  RETURN TRUE
END A089026;

PROCEDURE A091591 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR lo, hi, p, c: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; lo := Mu(n, n, ok); hi := Pw(Ad(n, 1, ok), 2, ok);
  c := 0; p := lo + 1;
  WHILE ok AND (p < hi) DO
    IF Prime(p) AND (p + 2 < hi) AND Prime(p + 2) THEN INC(c) END;
    INC(p)
  END;
  r := c; RETURN ok
END A091591;

PROCEDURE A093456 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR lo, hi, k, p: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; lo := Ad(Ch(n, 2, ok), 1, ok); hi := Ch(Ad(n, 1, ok), 2, ok);
  p := 1; k := lo;
  WHILE ok AND (k <= hi) DO
    IF (k > 1) AND NOT Prime(k) THEN p := Mu(p, k, ok) END;
    INC(k)
  END;
  r := p; RETURN ok
END A093456;

PROCEDURE A096535 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n <= 1 THEN r := 1; RETURN TRUE END;
  ok := TRUE; a0 := 1; a1 := 1; m := 2;
  WHILE ok AND (m <= n) DO
    a2 := Ad(a1, a0, ok) MOD m;
    a0 := a1; a1 := a2; INC(m)
  END;
  r := a1; RETURN ok
END A096535;

PROCEDURE A102371 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  ok := TRUE; a := 1; m := 2;
  WHILE ok AND (m <= n) DO a := NatArith.Xor(a, Ad(a, m, ok)); INC(m) END;
  r := a; RETURN ok
END A102371;

PROCEDURE A102847 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; a := 1; i := 0;
  WHILE ok AND (i < n) DO a := Ad(Mu(a, a, ok), 2, ok); INC(i) END;
  r := a; RETURN ok
END A102847;

PROCEDURE A103151 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR p, c, t: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; c := 0; p := 0;
  t := Ad(Mu(2, n, ok), 1, ok);
  WHILE ok AND (p <= n) DO
    IF (p # 2) AND (2 * p < t) AND Prime(p) AND Prime(t - 2 * p) THEN INC(c) END;
    INC(p)
  END;
  r := c; RETURN ok
END A103151;

PROCEDURE A103425 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, a3, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  IF n = 1 THEN r := 3; RETURN TRUE END;
  ok := TRUE; a0 := 1; a1 := 3; a2 := 5; m := 3;
  WHILE ok AND (m <= n) DO
    a3 := Sub(Ad(Mu(3, a2, ok), a1, ok), Mu(3, a0, ok));
    a0 := a1; a1 := a2; a2 := a3; INC(m)
  END;
  r := a2; RETURN ok
END A103425;

PROCEDURE A103885 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n) DO
    s := Ad(s, Mu(Ch(n, k, ok), Ch(Sub(Ad(Mu(2, n, ok), k, ok), 1), n - 1, ok), ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A103885;

PROCEDURE A104320 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR x, two, q: BigNat.T; d: CARDINAL; c: LONGCARD;
BEGIN
  IF n > 8000 THEN RETURN FALSE END;
  BigNat.FromNat(two, 2);
  IF NOT BigNat.Pow(two, n, x) THEN RETURN FALSE END;
  c := 0;
  WHILE NOT BigNat.IsZero(x) DO
    BigNat.DivModSmall(x, 3, q, d);
    IF d = 0 THEN INC(c) END;
    x := q
  END;
  r := c; RETURN TRUE
END A104320;

PROCEDURE A105020 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR c, k, i, m: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE;
  c := Sub(NatArith.Sqrt(Ad(Mu(8, n, ok), 1, ok)), 1) DIV 2;
  k := Sub(n, Ch(c + 1, 2, ok));
  i := Sub(c, k); m := c + 1;
  r := Sub(Mu(m, m, ok), Mu(i, i, ok));
  RETURN ok
END A105020;

PROCEDURE A105033 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k, p: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  (* 2^(k+1) <= n forces k + 1 < 64, so the remaining terms of range n are 0 *)
  WHILE ok AND (k < n) AND (k + 1 < 64) DO
    p := Pw(2, k + 1, ok);
    IF (p <= n) AND (n MOD p = k) THEN s := Ad(s, p, ok) END;
    INC(k)
  END;
  r := Sub(n, s); RETURN ok
END A105033;

PROCEDURE SumSmallerPrimeFactors (n: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
VAR f: ModArith.Factored; i: CARDINAL; s: LONGCARD;
BEGIN
  ModArith.Factor(n, f);
  s := 0; i := 0;
  WHILE i < f.count DO
    IF f.p[i] < n THEN s := Ad(s, f.p[i], ok) END;
    INC(i)
  END;
  RETURN s
END SumSmallerPrimeFactors;

PROCEDURE A105210 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  ok := TRUE; a := 393; m := 2;
  WHILE ok AND (m <= n) DO
    a := Ad(Ad(a, 1, ok), SumSmallerPrimeFactors(a, ok), ok);
    INC(m)
  END;
  r := a; RETURN ok
END A105210;

PROCEDURE A105801 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a1, a2, f, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n <= 2 THEN r := n; RETURN TRUE END;            (* 0, 1, 2 *)
  ok := TRUE; a1 := 1; a2 := 2; m := 3;
  WHILE ok AND (m <= n) DO
    f := Ad(a2, a1, ok);
    a1 := a2;
    IF ODD(f) THEN a2 := Ad(Mu(3, f, ok), 1, ok) ELSE a2 := f DIV 2 END;
    INC(m)
  END;
  r := a2; RETURN ok
END A105801;

PROCEDURE A107247 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR w: ARRAY [0..8] OF LONGCARD; k, v, s: LONGCARD; i: CARDINAL; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0;
  FOR i := 0 TO 8 DO w[i] := 0 END;          (* w holds nonacci (k-9) .. nonacci (k-1) *)
  k := 0;
  WHILE ok AND (k < Ad(n, 2, ok)) DO
    IF k < 8 THEN v := 0
    ELSIF k = 8 THEN v := 1
    ELSE
      v := 0;
      FOR i := 0 TO 8 DO v := Ad(v, w[i], ok) END
    END;
    s := Ad(s, Mu(v, v, ok), ok);
    FOR i := 0 TO 7 DO w[i] := w[i + 1] END;
    w[8] := v;
    INC(k)
  END;
  r := s; RETURN ok
END A107247;

PROCEDURE A108081 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k, f: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n) DO
    IF NOT Combinatorics.Fib(n - k + 1, f) THEN ok := FALSE END;
    s := Ad(s, Mu(Ch(Sub(Ad(n, k, ok), 1), k, ok), f, ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A108081;

PROCEDURE A108211 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR ok: BOOLEAN;
BEGIN
  ok := TRUE; r := Ad(Mu(16, Mu(n, n, ok), ok), 1, ok);
  RETURN ok
END A108211;

PROCEDURE A108301 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR x, two: BigNat.T; e: LONGCARD; s: ARRAY [0..2600] OF CHAR; i: CARDINAL;
BEGIN
  IF n > 12 THEN RETURN FALSE END;
  e := 1; i := 0;
  WHILE VAL(LONGCARD, i) < n DO e := e * 2; INC(i) END;
  BigNat.FromNat(two, 2);
  IF NOT BigNat.Pow(two, e, x) OR NOT BigNat.AddSmall(x, 1, x) THEN RETURN FALSE END;
  IF NOT BigNat.ToDecimal(x, s) THEN RETURN FALSE END;
  r := 0; i := 0;
  WHILE (i <= HIGH(s)) AND (s[i] # 0C) DO
    r := r + VAL(LONGCARD, ORD(s[i]) - ORD('0')); INC(i)
  END;
  RETURN TRUE
END A108301;

PROCEDURE A108306 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  ok := TRUE; a0 := 1; a1 := 6; m := 2;
  WHILE ok AND (m <= n) DO
    a2 := Ad(Mu(3, a1, ok), Mu(3, a0, ok), ok);
    a0 := a1; a1 := a2; INC(m)
  END;
  r := a1; RETURN ok
END A108306;

PROCEDURE A109671 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR i, k: CARDINAL; p, q: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > MemoMax THEN RETURN FALSE END;
  memo[0] := 0; memo[1] := 1; ok := TRUE;
  i := 2;
  WHILE ok AND (VAL(LONGCARD, i) <= n) DO
    IF i MOD 2 = 0 THEN memo[i] := memo[i DIV 2]
    ELSE
      k := (i - 1) DIV 2; p := memo[i - 2]; q := memo[k];
      IF p > q THEN memo[i] := p - q ELSE memo[i] := Ad(p, q, ok) END
    END;
    INC(i)
  END;
  r := memo[VAL(CARDINAL, n)]; RETURN ok
END A109671;

PROCEDURE A109845 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, m, sq: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 2; RETURN TRUE END;
  ok := TRUE; a := 3; m := 2;
  WHILE ok AND (m <= n) DO
    sq := Mu(a, a, ok);
    IF (m - 2) MOD 2 = 0 THEN a := Sub(sq, Ad(a, 1, ok)) ELSE a := Ad(Ad(sq, a, ok), 1, ok) END;
    INC(m)
  END;
  r := a; RETURN ok
END A109845;

PROCEDURE A109905 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k, v, best: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; best := 0; k := 1;
  WHILE ok AND (k <= n DIV 2) DO
    v := Ad(Mu(k, n - k, ok), 1, ok);
    IF ok AND Prime(v) AND (v > best) THEN best := v END;
    INC(k)
  END;
  r := best; RETURN ok
END A109905;

PROCEDURE A109908 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k, v, best: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; best := 0; k := 1;
  WHILE ok AND (k <= n DIV 2) DO
    v := Sub(Mu(k, n - k, ok), 1);
    IF ok AND Prime(v) AND (v > best) THEN best := v END;
    INC(k)
  END;
  r := best; RETURN ok
END A109908;

PROCEDURE A109909 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k: LONGCARD; i: CARDINAL; c: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > VAL(LONGCARD, NatSeq.MaxLen) + 1 THEN RETURN FALSE END;
  ok := TRUE; NatSeq.Clear(setA); k := 1;
  WHILE ok AND (k < n) DO                              (* image of Ico 1 n *)
    ok := NatSeq.Push(setA, Sub(Mu(k, n - k, ok), 1));
    INC(k)
  END;
  NatSeq.ToFinset(setA);
  c := 0; i := 0;
  WHILE i < setA.len DO
    IF Prime(setA.x[i]) THEN INC(c) END;
    INC(i)
  END;
  r := c; RETURN ok
END A109909;

PROCEDURE A111291 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR m, d, j: CARDINAL; c: LONGCARD; ok: BOOLEAN; x: LONGCARD;
BEGIN
  ok := TRUE; x := Pw(10, n, ok);
  IF NOT ok OR (x > MemoMax) THEN RETURN FALSE END;
  m := VAL(CARDINAL, x);
  FOR j := 1 TO m DO memo[j] := 0 END;               (* memo[k] = #divisors k *)
  FOR d := 1 TO m DO
    j := d;
    WHILE j <= m DO INC(memo[j]); INC(j, d) END
  END;
  c := 0;
  FOR j := 1 TO m DO
    IF VAL(LONGCARD, j) MOD memo[j] = 0 THEN INC(c) END
  END;
  r := c; RETURN TRUE
END A111291;

PROCEDURE A112970 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR i, k: CARDINAL; ok: BOOLEAN;
BEGIN
  IF n > MemoMax THEN RETURN FALSE END;
  memo[0] := 1; memo[1] := 1; ok := TRUE; i := 2;
  WHILE ok AND (VAL(LONGCARD, i) <= n) DO
    k := i DIV 2;
    IF i MOD 2 = 1 THEN memo[i] := memo[k]
    ELSIF k < 2 THEN memo[i] := memo[k]
    ELSE memo[i] := Ad(memo[k], memo[k - 2], ok) END;
    INC(i)
  END;
  r := memo[VAL(CARDINAL, n)]; RETURN ok
END A112970;

PROCEDURE A113010 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  RETURN NatArith.Pow(Digits.Length(10, n), Digits.Sum(10, n), r)
END A113010;

PROCEDURE A113213 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR x, m: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; x := Pw(2, n, ok);
  IF NOT ok OR (x >= 9223372036854775808) THEN RETURN FALSE END;   (* x + m must fit *)
  m := 0;
  WHILE m <= x DO
    IF Prime(x - m) AND Prime(x + m) THEN r := m; RETURN TRUE END;
    INC(m)
  END;
  r := 0; RETURN TRUE
END A113213;

PROCEDURE A113257 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, i, e: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; i := 1;
  WHILE ok AND (i <= n) DO
    e := Pw(n - i + 1, 2, ok);
    IF i = 1 THEN s := Ad(s, 1, ok)                      (* (1^2)^e = 1 for every e *)
    ELSE s := Ad(s, Pw(Mu(i, i, ok), e, ok), ok) END;
    INC(i)
  END;
  r := s; RETURN ok
END A113257;

PROCEDURE A113258 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, i, b: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; i := 0;
  WHILE ok AND (i < n) DO
    b := Fa(i + 1, ok);
    IF b = 1 THEN s := Ad(s, 1, ok)                      (* 1^e = 1 for every e *)
    ELSE s := Ad(s, Pw(b, Fa(n - i, ok), ok), ok) END;
    INC(i)
  END;
  r := s; RETURN ok
END A113258;

PROCEDURE A113271 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; i := 0;
  WHILE ok AND (i <= n) DO
    IF i = 0 THEN s := Ad(s, 1, ok)                      (* 2^(0 * _) = 1 *)
    ELSE s := Ad(s, Pw(2, Mu(i, Pw(2, n - i, ok), ok), ok), ok) END;
    INC(i)
  END;
  r := s; RETURN ok
END A113271;

PROCEDURE OeisPrimePower (q: LONGCARD) : BOOLEAN;
VAR f: ModArith.Factored;
BEGIN
  IF q = 1 THEN RETURN TRUE END;
  IF q = 0 THEN RETURN FALSE END;
  ModArith.Factor(q, f);
  RETURN f.count = 1
END OeisPrimePower;

PROCEDURE A113609 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR q, c: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; c := 0; q := 1;
  WHILE ok AND (q <= n) DO
    IF OeisPrimePower(q) AND OeisPrimePower(Ad(q, 2, ok)) THEN INC(c) END;
    INC(q)
  END;
  r := c; RETURN ok
END A113609;

PROCEDURE A115257 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k, c: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n) DO
    IF NOT Combinatorics.CentralBinom(k, c) THEN ok := FALSE END;
    s := Ad(s, Mu(c, c, ok), ok); INC(k)
  END;
  r := s; RETURN ok
END A115257;

PROCEDURE A115366 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR k, m, c: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > 5 THEN RETURN FALSE END;
  ok := TRUE; m := Pw(10, n, ok); c := 0; k := 1;
  WHILE k <= m DO
    IF Prime(k * k + 3 * k + 1) THEN INC(c) END;
    INC(k)
  END;
  r := c; RETURN ok
END A115366;

PROCEDURE A119563 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR ok: BOOLEAN; t: LONGCARD;
BEGIN
  ok := TRUE; t := Pw(2, n, ok);
  r := Sub(Ad(Pw(2, t, ok), t, ok), 1);
  RETURN ok
END A119563;

PROCEDURE Half (x: LONGCARD) : LONGCARD;
BEGIN
  IF x MOD 2 = 0 THEN RETURN x DIV 2 END;
  RETURN x
END Half;

PROCEDURE A120424 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;
  ok := TRUE; a0 := 1; a1 := 3; m := 2;
  WHILE ok AND (m <= n) DO
    a2 := Ad(Half(a1), Half(a0), ok);
    a0 := a1; a1 := a2; INC(m)
  END;
  r := a1; RETURN ok
END A120424;

PROCEDURE A135508 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR x, xn, m, l: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  ok := TRUE; x := 1; m := 1;                    (* x = x m; x (m+1) = 2 x m + lcm (x m) (m+1) *)
  xn := 0;
  WHILE ok AND (m <= n) DO
    IF m = n THEN xn := x END;
    IF NOT NumberTheory.Lcm(x, m + 1, l) THEN ok := FALSE END;
    x := Ad(Mu(2, x, ok), l, ok);
    INC(m)
  END;
  r := Sub(NatArith.Div(x, xn), 2); RETURN ok
END A135508;

PROCEDURE A141057 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, inner, k, j: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n) DO
    inner := 0; j := 0;
    WHILE ok AND (j <= k) DO inner := Ad(inner, Pw(Ch(k, j, ok), 3, ok), ok); INC(j) END;
    s := Ad(s, Mu(Pw(Ch(n, k, ok), 3, ok), inner, ok), ok);
    INC(k)
  END;
  r := s; RETURN ok
END A141057;

PROCEDURE Count2xcy (n, c, res: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* ∑_{x, y ∈ [1, N]} [2^x + c 2^y < N ∧ N - (2^x + c 2^y) prime ∧ … % 6 = res], N = 2n - 1.
   Terms with 2^x + c 2^y ≥ N vanish, so x and y stop once a power reaches N. *)
VAR nn, x, y, px, py, t, cnt: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  IF n > 4611686018427387904 THEN RETURN FALSE END;
  nn := 2 * n - 1; cnt := 0;
  x := 1; px := 2;
  WHILE (x <= nn) AND (px < nn) DO
    y := 1; py := 2;
    WHILE (y <= nn) AND (py <= (nn - px) DIV c) DO
      t := px + c * py;
      IF (t < nn) AND ((nn - t) MOD 6 = res) AND Prime(nn - t) THEN INC(cnt) END;
      INC(y); py := py * 2
    END;
    INC(x); px := px * 2
  END;
  r := cnt; RETURN TRUE
END Count2xcy;

PROCEDURE A157225 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Count2xcy(n, 7, 5, r)
END A157225;

PROCEDURE A157237 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Count2xcy(n, 11, 1, r)
END A157237;

PROCEDURE Polygonal (k, x: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
BEGIN
  RETURN Ad(Mu(Sub(k, 2), Mu(x, Sub(x, 1), ok) DIV 2, ok), x, ok)
END Polygonal;

PROCEDURE A160324 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* a value that overflows exceeds n, so such a term is 0 exactly as in ℕ *)
VAR b, x, y, z, c, v: LONGCARD; ok: BOOLEAN;
BEGIN
  b := NatArith.Sqrt(n) + 2; c := 0;
  FOR x := 0 TO b - 1 DO
    FOR y := 0 TO b - 1 DO
      FOR z := 0 TO b - 1 DO
        ok := TRUE;
        v := Ad(Ad(Mu(x, x, ok), Polygonal(5, y, ok), ok), Polygonal(6, z, ok), ok);
        IF ok AND (v = n) THEN INC(c) END
      END
    END
  END;
  r := c; RETURN TRUE
END A160324;

PROCEDURE A166944 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  ok := TRUE; a := 2; m := 2;
  WHILE ok AND (m <= n) DO
    IF m MOD 2 = 0 THEN a := Ad(a, NumberTheory.Gcd(m, a), ok)
    ELSE a := Ad(a, NumberTheory.Gcd(m - 2, a), ok) END;
    INC(m)
  END;
  r := a; RETURN ok
END A166944;

PROCEDURE NextA167604 (m: LONGCARD; VAR ok: BOOLEAN) : LONGCARD;
(* minFac (∏_{d ∣ m} (d + m/d)). Every factor is ≥ 2, so the least prime factor of the
   product is the least of the factors' least prime factors; the product is never formed. *)
VAR f: ModArith.Factored; idx: ARRAY [0..ModArith.MaxFactors - 1] OF CARDINAL;
    d, best, mf: LONGCARD; i: CARDINAL; done: BOOLEAN;
BEGIN
  IF m = 0 THEN RETURN 1 END;                         (* empty product: minFac 1 = 1 *)
  ModArith.Factor(m, f);
  FOR i := 0 TO ModArith.MaxFactors - 1 DO idx[i] := 0 END;
  best := 0; done := FALSE;
  REPEAT
    d := 1; i := 0;
    WHILE i < f.count DO d := d * Pw(f.p[i], VAL(LONGCARD, idx[i]), ok); INC(i) END;
    mf := ModArith.MinFacFast(Ad(d, m DIV d, ok));
    IF (best = 0) OR (mf < best) THEN best := mf END;
    (* advance the mixed-radix exponent counter *)
    i := 0;
    LOOP
      IF i >= f.count THEN done := TRUE; EXIT END;
      IF idx[i] < f.e[i] THEN INC(idx[i]); EXIT END;
      idx[i] := 0; INC(i)
    END
  UNTIL done;
  RETURN best
END NextA167604;

PROCEDURE A167604 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR prod, a, i: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; prod := 1; a := 1; i := 0;
  WHILE ok AND (i < n) DO
    a := NextA167604(prod, ok);
    prod := Mu(prod, a, ok);
    INC(i)
  END;
  r := a; RETURN ok
END A167604;

PROCEDURE A181391 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* memo[v] = 1 + the last step index at which v was the current value; 0 = never *)
VAR i, cur, nxt: CARDINAL;
BEGIN
  IF n > MemoMax THEN RETURN FALSE END;
  FOR i := 0 TO VAL(CARDINAL, n) DO memo[i] := 0 END;
  cur := 0; i := 0;
  WHILE VAL(LONGCARD, i) < n DO
    IF memo[cur] # 0 THEN nxt := i - VAL(CARDINAL, memo[cur] - 1) ELSE nxt := 0 END;
    memo[cur] := VAL(LONGCARD, i) + 1;
    cur := nxt; INC(i)
  END;
  r := VAL(LONGCARD, cur); RETURN TRUE
END A181391;

PROCEDURE A181546 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR s, k: LONGCARD; ok: BOOLEAN;
BEGIN
  ok := TRUE; s := 0; k := 0;
  WHILE ok AND (k <= n DIV 2) DO s := Ad(s, Pw(Ch(n - k, k, ok), 4, ok), ok); INC(k) END;
  r := s; RETURN ok
END A181546;

PROCEDURE A185150 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR lo, hi, p, c: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n >= 4294967296 THEN RETURN FALSE END;
  ok := TRUE; lo := n * n; hi := Pw(n + 1, 2, ok); c := 0; p := lo + 1;
  WHILE ok AND (p < hi) DO
    IF (p # 2) AND Prime(p) AND (NumberTheory.Jacobi(VAL(LONGINT, n), p) = 1) THEN INC(c) END;
    INC(p)
  END;
  r := c; RETURN ok
END A185150;

PROCEDURE A260194 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a0, a1, a2, a3, m: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n <= 2 THEN r := 1; RETURN TRUE END;
  ok := TRUE; a0 := 1; a1 := 1; a2 := 1; m := 3;
  WHILE ok AND (m <= n) DO
    a3 := Ad(a2, NumberTheory.Gcd(a2, a0), ok);
    a0 := a1; a1 := a2; a2 := a3; INC(m)
  END;
  r := a2; RETURN ok
END A260194;

PROCEDURE A358684 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* 2^n - log2 (minFac (fermatNumber n)). For n <= 4 the Fermat number fits in 64 bits.
   For n >= 5 every prime factor of F_n is ≡ 1 (mod 2^(n+2)) (Euler–Lucas), so the least
   candidate k·2^(n+2) + 1 dividing F_n is its least prime factor; candidates are tried below
   2^32 and the result is FALSE if none divides. *)
VAR f, p, step: LONGCARD; ok: BOOLEAN; F, two, q: BigNat.T; rem: CARDINAL;
BEGIN
  IF n <= 4 THEN
    ok := TRUE; f := Ad(Pw(2, Pw(2, n, ok), ok), 1, ok);
    p := ModArith.MinFacFast(f);
    r := Sub(Pw(2, n, ok), NatArith.Log2(p));
    RETURN ok
  END;
  IF n > 12 THEN RETURN FALSE END;                    (* F_13 exceeds BigNat's capacity *)
  BigNat.FromNat(two, 2);
  IF NOT BigNat.Pow(two, Pw2(n), F) OR NOT BigNat.AddSmall(F, 1, F) THEN RETURN FALSE END;
  step := Pw2(n + 2); p := step + 1;
  WHILE p < 4294967296 DO
    BigNat.DivModSmall(F, VAL(CARDINAL, p), q, rem);
    IF rem = 0 THEN r := Pw2(n) - NatArith.Log2(p); RETURN TRUE END;
    p := p + step
  END;
  RETURN FALSE
END A358684;

PROCEDURE A368633 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a: ARRAY [0..4096] OF LONGCARD; m, k: CARDINAL; s: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > 4096 THEN RETURN FALSE END;
  a[0] := 1; ok := TRUE; m := 1;
  WHILE ok AND (VAL(LONGCARD, m) <= n) DO
    s := 0;
    FOR k := 0 TO m - 1 DO s := Ad(s, Mu(a[k], a[m - 1 - k], ok), ok) END;
    IF m MOD 2 = 0 THEN s := Mu(3, s, ok) END;
    a[m] := s; INC(m)
  END;
  r := a[VAL(CARDINAL, n)]; RETURN ok
END A368633;

PROCEDURE A375439 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* b m = a m for m < n and 0 at n; with a 0 = 0 the k = 0 and k = n terms of conv3 vanish,
   and conv2 b k for k < n equals the stored c2[k] *)
VAR a, c2: ARRAY [0..4096] OF LONGCARD; m, k, j: CARDINAL; s, sub: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > 4096 THEN RETURN FALSE END;
  a[0] := 0; a[1] := 1; a[2] := 1;
  c2[0] := 0; c2[1] := 0; c2[2] := 1;               (* conv2 a 0, 1, 2 *)
  IF n <= 2 THEN r := a[VAL(CARDINAL, n)]; RETURN TRUE END;
  ok := TRUE; m := 3;
  WHILE ok AND (VAL(LONGCARD, m) <= n) DO
    s := 0;
    FOR k := 1 TO m - 1 DO s := Ad(s, Mu(c2[k], a[m - k], ok), ok) END;
    IF m MOD 3 = 0 THEN sub := a[m DIV 3] ELSE sub := 0 END;
    a[m] := Ad(Mu(2, s, ok), sub, ok) DIV 3;
    s := 0;                                          (* c2[m] = conv2 a m, now that a m is known *)
    FOR j := 0 TO m DO s := Ad(s, Mu(a[j], a[m - j], ok), ok) END;
    c2[m] := s;
    INC(m)
  END;
  r := a[VAL(CARDINAL, n)]; RETURN ok
END A375439;

PROCEDURE A397588 (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR a: ARRAY [0..4096] OF LONGCARD; m, k: CARDINAL; s: LONGCARD; ok: BOOLEAN;
BEGIN
  IF n > 4096 THEN RETURN FALSE END;
  a[0] := 0; a[1] := 1;
  IF n <= 1 THEN r := n; RETURN TRUE END;
  ok := TRUE; m := 2;
  WHILE ok AND (VAL(LONGCARD, m) <= n) DO
    s := 0;
    FOR k := 1 TO m - 1 DO s := Ad(s, Mu(a[k], a[m - k], ok), ok) END;
    a[m] := Mu(VAL(LONGCARD, m + 1), s, ok); INC(m)
  END;
  r := a[VAL(CARDINAL, n)]; RETURN ok
END A397588;

END OeisNat.
