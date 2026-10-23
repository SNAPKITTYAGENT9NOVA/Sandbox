(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE NatSeq;

IMPORT NatArith, NumberTheory;

PROCEDURE Clear (VAR l: T);
BEGIN
  l.len := 0
END Clear;

PROCEDURE Push (VAR l: T; v: LONGCARD) : BOOLEAN;
BEGIN
  IF l.len >= MaxLen THEN RETURN FALSE END;
  l.x[l.len] := v; INC(l.len);
  RETURN TRUE
END Push;

PROCEDURE Icc (a, b: LONGCARD; VAR l: T) : BOOLEAN;
VAR
  v: LONGCARD;
BEGIN
  l.len := 0;
  IF a > b THEN RETURN TRUE END;
  IF b - a >= VAL(LONGCARD, MaxLen) THEN RETURN FALSE END;
  v := a;
  LOOP
    l.x[l.len] := v; INC(l.len);
    IF v = b THEN EXIT END;
    INC(v)
  END;
  RETURN TRUE
END Icc;

PROCEDURE Ico (a, b: LONGCARD; VAR l: T) : BOOLEAN;
BEGIN
  IF b <= a THEN l.len := 0; RETURN TRUE END;
  RETURN Icc(a, b - 1, l)
END Ico;

PROCEDURE Ioc (a, b: LONGCARD; VAR l: T) : BOOLEAN;
BEGIN
  IF b <= a THEN l.len := 0; RETURN TRUE END;
  RETURN Icc(a + 1, b, l)
END Ioc;

PROCEDURE Range (n: LONGCARD; VAR l: T) : BOOLEAN;
BEGIN
  RETURN Ico(0, n, l)
END Range;

PROCEDURE Get (VAR l: T; i: LONGCARD) : LONGCARD;
BEGIN
  IF i >= VAL(LONGCARD, l.len) THEN RETURN 0 END;
  RETURN l.x[VAL(CARDINAL, i)]
END Get;

PROCEDURE Head (VAR l: T; dflt: LONGCARD) : LONGCARD;
BEGIN
  IF l.len = 0 THEN RETURN dflt END;
  RETURN l.x[0]
END Head;

PROCEDURE Last (VAR l: T; dflt: LONGCARD) : LONGCARD;
BEGIN
  IF l.len = 0 THEN RETURN dflt END;
  RETURN l.x[l.len - 1]
END Last;

PROCEDURE Filter (VAR l: T; p: Pred; VAR r: T);
VAR
  i, k: CARDINAL; v: LONGCARD;
BEGIN
  k := 0; i := 0;               (* r may alias l: k <= i always holds *)
  WHILE i < l.len DO
    v := l.x[i];
    IF p(v) THEN r.x[k] := v; INC(k) END;
    INC(i)
  END;
  r.len := k
END Filter;

PROCEDURE Map (VAR l: T; f: Fn; VAR r: T);
VAR
  i, n: CARDINAL;
BEGIN
  n := l.len; i := 0;
  WHILE i < n DO r.x[i] := f(l.x[i]); INC(i) END;
  r.len := n
END Map;

PROCEDURE Append (VAR a, b: T; VAR r: T) : BOOLEAN;
VAR
  i, na, nb: CARDINAL;
BEGIN
  na := a.len; nb := b.len;
  IF na + nb > MaxLen THEN RETURN FALSE END;
  (* copy b first (from the top) so that r aliasing a or b is safe *)
  i := nb;
  WHILE i > 0 DO DEC(i); r.x[na + i] := b.x[i] END;
  i := 0;
  WHILE i < na DO r.x[i] := a.x[i]; INC(i) END;
  r.len := na + nb;
  RETURN TRUE
END Append;

PROCEDURE Reverse (VAR l: T; VAR r: T);
VAR
  i, j, n: CARDINAL; t: LONGCARD;
BEGIN
  n := l.len;
  i := 0;
  WHILE i < n DO r.x[i] := l.x[i]; INC(i) END;
  r.len := n;
  IF n < 2 THEN RETURN END;
  i := 0; j := n - 1;
  WHILE i < j DO
    t := r.x[i]; r.x[i] := r.x[j]; r.x[j] := t;
    INC(i); DEC(j)
  END
END Reverse;

PROCEDURE Take (VAR l: T; n: LONGCARD; VAR r: T);
VAR
  i, m: CARDINAL;
BEGIN
  IF n < VAL(LONGCARD, l.len) THEN m := VAL(CARDINAL, n) ELSE m := l.len END;
  i := 0;
  WHILE i < m DO r.x[i] := l.x[i]; INC(i) END;
  r.len := m
END Take;

PROCEDURE Drop (VAR l: T; n: LONGCARD; VAR r: T);
VAR
  i, s, m: CARDINAL;
BEGIN
  IF n >= VAL(LONGCARD, l.len) THEN r.len := 0; RETURN END;
  s := VAL(CARDINAL, n); m := l.len - s;
  i := 0;
  WHILE i < m DO r.x[i] := l.x[s + i]; INC(i) END;
  r.len := m
END Drop;

PROCEDURE Sum (VAR l: T; VAR s: LONGCARD) : BOOLEAN;
VAR
  i: CARDINAL; acc: LONGCARD;
BEGIN
  acc := 0; i := 0;
  WHILE i < l.len DO
    IF NOT NatArith.Add(acc, l.x[i], acc) THEN RETURN FALSE END;
    INC(i)
  END;
  s := acc; RETURN TRUE
END Sum;

PROCEDURE Prod (VAR l: T; VAR p: LONGCARD) : BOOLEAN;
VAR
  i: CARDINAL; acc: LONGCARD;
BEGIN
  acc := 1; i := 0;
  (* a zero factor makes the product 0 even if an earlier partial product overflowed *)
  WHILE i < l.len DO
    IF l.x[i] = 0 THEN p := 0; RETURN TRUE END;
    INC(i)
  END;
  i := 0;
  WHILE i < l.len DO
    IF NOT NatArith.Mul(acc, l.x[i], acc) THEN RETURN FALSE END;
    INC(i)
  END;
  p := acc; RETURN TRUE
END Prod;

PROCEDURE Count (VAR l: T; v: LONGCARD) : LONGCARD;
VAR
  i: CARDINAL; c: LONGCARD;
BEGIN
  c := 0; i := 0;
  WHILE i < l.len DO
    IF l.x[i] = v THEN INC(c) END;
    INC(i)
  END;
  RETURN c
END Count;

PROCEDURE CountP (VAR l: T; p: Pred) : LONGCARD;
VAR
  i: CARDINAL; c: LONGCARD;
BEGIN
  c := 0; i := 0;
  WHILE i < l.len DO
    IF p(l.x[i]) THEN INC(c) END;
    INC(i)
  END;
  RETURN c
END CountP;

PROCEDURE Mem (VAR l: T; v: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Count(l, v) > 0
END Mem;

PROCEDURE All (VAR l: T; p: Pred) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  i := 0;
  WHILE i < l.len DO
    IF NOT p(l.x[i]) THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END All;

PROCEDURE Any (VAR l: T; p: Pred) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  i := 0;
  WHILE i < l.len DO
    IF p(l.x[i]) THEN RETURN TRUE END;
    INC(i)
  END;
  RETURN FALSE
END Any;

PROCEDURE IndexOf (VAR l: T; v: LONGCARD) : LONGCARD;
VAR
  i: CARDINAL;
BEGIN
  i := 0;
  WHILE i < l.len DO
    IF l.x[i] = v THEN RETURN VAL(LONGCARD, i) END;
    INC(i)
  END;
  RETURN VAL(LONGCARD, l.len)
END IndexOf;

PROCEDURE Sup (VAR l: T) : LONGCARD;
VAR
  i: CARDINAL; m: LONGCARD;
BEGIN
  m := 0; i := 0;
  WHILE i < l.len DO
    IF l.x[i] > m THEN m := l.x[i] END;
    INC(i)
  END;
  RETURN m
END Sup;

PROCEDURE Inf (VAR l: T; VAR m: LONGCARD) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  IF l.len = 0 THEN RETURN FALSE END;
  m := l.x[0]; i := 1;
  WHILE i < l.len DO
    IF l.x[i] < m THEN m := l.x[i] END;
    INC(i)
  END;
  RETURN TRUE
END Inf;

PROCEDURE IsSorted (VAR l: T) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  i := 1;
  WHILE i < l.len DO
    IF l.x[i - 1] > l.x[i] THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END IsSorted;

PROCEDURE Equal (VAR a, b: T) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  IF a.len # b.len THEN RETURN FALSE END;
  i := 0;
  WHILE i < a.len DO
    IF a.x[i] # b.x[i] THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Equal;

(* Bottom-up merge sort with a scratch buffer: O(n log n), stable. *)
VAR
  scratch: ARRAY [0..MaxLen - 1] OF LONGCARD;

PROCEDURE Sort (VAR l: T);
VAR
  width, lo, mid, hi, i, j, k, n: CARDINAL;
BEGIN
  n := l.len;
  width := 1;
  WHILE width < n DO
    lo := 0;
    WHILE lo < n DO
      mid := lo + width; IF mid > n THEN mid := n END;
      hi := lo + 2 * width; IF hi > n THEN hi := n END;
      i := lo; j := mid; k := lo;
      WHILE (i < mid) AND (j < hi) DO
        IF l.x[j] < l.x[i] THEN scratch[k] := l.x[j]; INC(j)
        ELSE scratch[k] := l.x[i]; INC(i) END;
        INC(k)
      END;
      WHILE i < mid DO scratch[k] := l.x[i]; INC(i); INC(k) END;
      WHILE j < hi DO scratch[k] := l.x[j]; INC(j); INC(k) END;
      lo := hi
    END;
    i := 0;
    WHILE i < n DO l.x[i] := scratch[i]; INC(i) END;
    width := width * 2
  END
END Sort;

PROCEDURE Nodup (VAR l: T) : BOOLEAN;      (* sorts a copy: O(n log n) *)
VAR
  c: T; i: CARDINAL;
BEGIN
  c.len := l.len; i := 0;
  WHILE i < l.len DO c.x[i] := l.x[i]; INC(i) END;
  Sort(c);
  i := 1;
  WHILE i < c.len DO
    IF c.x[i - 1] = c.x[i] THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Nodup;

PROCEDURE Dedup (VAR l: T);
VAR
  i, j, k: CARDINAL; seen: BOOLEAN;
BEGIN
  k := 0; i := 0;
  WHILE i < l.len DO
    seen := FALSE; j := 0;
    WHILE (j < k) AND NOT seen DO
      IF l.x[j] = l.x[i] THEN seen := TRUE END;
      INC(j)
    END;
    IF NOT seen THEN l.x[k] := l.x[i]; INC(k) END;
    INC(i)
  END;
  l.len := k
END Dedup;

PROCEDURE ToFinset (VAR l: T);
VAR
  i, k: CARDINAL;
BEGIN
  Sort(l);
  IF l.len = 0 THEN RETURN END;
  k := 1; i := 1;
  WHILE i < l.len DO
    IF l.x[i] # l.x[k - 1] THEN l.x[k] := l.x[i]; INC(k) END;
    INC(i)
  END;
  l.len := k
END ToFinset;

PROCEDURE FinsetMem (VAR s: T; v: LONGCARD) : BOOLEAN;
VAR
  lo, hi, mid: CARDINAL;
BEGIN
  lo := 0; hi := s.len;
  WHILE lo < hi DO
    mid := lo + (hi - lo) DIV 2;
    IF s.x[mid] = v THEN RETURN TRUE
    ELSIF s.x[mid] < v THEN lo := mid + 1
    ELSE hi := mid END
  END;
  RETURN FALSE
END FinsetMem;

PROCEDURE Union (VAR a, b: T; VAR r: T) : BOOLEAN;
VAR
  i, j, k: CARDINAL;
BEGIN
  i := 0; j := 0; k := 0;
  WHILE (i < a.len) OR (j < b.len) DO
    IF k >= MaxLen THEN RETURN FALSE END;
    IF j >= b.len THEN scratch[k] := a.x[i]; INC(i)
    ELSIF i >= a.len THEN scratch[k] := b.x[j]; INC(j)
    ELSIF a.x[i] < b.x[j] THEN scratch[k] := a.x[i]; INC(i)
    ELSIF b.x[j] < a.x[i] THEN scratch[k] := b.x[j]; INC(j)
    ELSE scratch[k] := a.x[i]; INC(i); INC(j) END;
    INC(k)
  END;
  i := 0;
  WHILE i < k DO r.x[i] := scratch[i]; INC(i) END;
  r.len := k;
  RETURN TRUE
END Union;

PROCEDURE Inter (VAR a, b: T; VAR r: T);
VAR
  i, j, k: CARDINAL;
BEGIN
  i := 0; j := 0; k := 0;
  WHILE (i < a.len) AND (j < b.len) DO
    IF a.x[i] < b.x[j] THEN INC(i)
    ELSIF b.x[j] < a.x[i] THEN INC(j)
    ELSE scratch[k] := a.x[i]; INC(k); INC(i); INC(j) END
  END;
  i := 0;
  WHILE i < k DO r.x[i] := scratch[i]; INC(i) END;
  r.len := k
END Inter;

PROCEDURE Diff (VAR a, b: T; VAR r: T);
VAR
  i, j, k: CARDINAL;
BEGIN
  i := 0; j := 0; k := 0;
  WHILE i < a.len DO
    WHILE (j < b.len) AND (b.x[j] < a.x[i]) DO INC(j) END;
    IF (j >= b.len) OR (b.x[j] # a.x[i]) THEN scratch[k] := a.x[i]; INC(k) END;
    INC(i)
  END;
  i := 0;
  WHILE i < k DO r.x[i] := scratch[i]; INC(i) END;
  r.len := k
END Diff;

PROCEDURE Subset (VAR a, b: T) : BOOLEAN;
VAR
  i: CARDINAL;
BEGIN
  i := 0;
  WHILE i < a.len DO
    IF NOT FinsetMem(b, a.x[i]) THEN RETURN FALSE END;
    INC(i)
  END;
  RETURN TRUE
END Subset;

PROCEDURE Image (VAR s: T; f: Fn; VAR r: T);
BEGIN
  Map(s, f, r);
  ToFinset(r)
END Image;

PROCEDURE Divisors (n: LONGCARD; VAR l: T) : BOOLEAN;
VAR
  d, q: LONGCARD; lo, hi: CARDINAL;
  high: ARRAY [0..MaxLen - 1] OF LONGCARD;
BEGIN
  l.len := 0; hi := 0;
  IF n = 0 THEN RETURN TRUE END;
  d := 1;
  WHILE d <= n DIV d DO
    IF n MOD d = 0 THEN
      q := n DIV d;
      IF l.len + hi + 2 > MaxLen THEN l.len := 0; RETURN FALSE END;
      l.x[l.len] := d; INC(l.len);
      IF q # d THEN high[hi] := q; INC(hi) END
    END;
    INC(d)
  END;
  lo := hi;
  WHILE lo > 0 DO DEC(lo); l.x[l.len] := high[lo]; INC(l.len) END;
  RETURN TRUE
END Divisors;

PROCEDURE ProperDivisors (n: LONGCARD; VAR l: T) : BOOLEAN;
BEGIN
  IF NOT Divisors(n, l) THEN RETURN FALSE END;
  IF l.len > 0 THEN DEC(l.len) END;             (* drop n itself, the last divisor *)
  RETURN TRUE
END ProperDivisors;

PROCEDURE PrimeFactorsList (n: LONGCARD; VAR l: T) : BOOLEAN;
VAR
  m, p: LONGCARD;
BEGIN
  l.len := 0;
  IF n <= 1 THEN RETURN TRUE END;
  m := n;
  WHILE m > 1 DO
    p := NumberTheory.MinFac(m);
    IF l.len >= MaxLen THEN l.len := 0; RETURN FALSE END;
    l.x[l.len] := p; INC(l.len);
    m := m DIV p
  END;
  RETURN TRUE
END PrimeFactorsList;

PROCEDURE PrimeFactors (n: LONGCARD; VAR l: T) : BOOLEAN;
BEGIN
  IF NOT PrimeFactorsList(n, l) THEN RETURN FALSE END;
  ToFinset(l);
  RETURN TRUE
END PrimeFactors;

PROCEDURE PrimesBelow (n: LONGCARD; VAR l: T) : BOOLEAN;
VAR
  sieve: ARRAY [0..65535] OF BOOLEAN;
  i, j, m: CARDINAL;
BEGIN
  l.len := 0;
  IF n <= 2 THEN RETURN TRUE END;
  IF n > 65536 THEN RETURN FALSE END;
  m := VAL(CARDINAL, n);
  FOR i := 0 TO m - 1 DO sieve[i] := TRUE END;
  sieve[0] := FALSE; sieve[1] := FALSE;
  i := 2;
  WHILE i * i < m DO
    IF sieve[i] THEN
      j := i * i;
      WHILE j < m DO sieve[j] := FALSE; INC(j, i) END
    END;
    INC(i)
  END;
  FOR i := 2 TO m - 1 DO
    IF sieve[i] THEN
      IF l.len >= MaxLen THEN l.len := 0; RETURN FALSE END;
      l.x[l.len] := VAL(LONGCARD, i); INC(l.len)
    END
  END;
  RETURN TRUE
END PrimesBelow;

END NatSeq.
