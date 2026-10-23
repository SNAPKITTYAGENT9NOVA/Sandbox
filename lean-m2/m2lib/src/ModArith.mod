(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE ModArith;

IMPORT NatArith, NumberTheory;
FROM NumberTheory IMPORT MulMod, PowMod, AddMod, Gcd;
FROM Storage IMPORT ALLOCATE, DEALLOCATE;

CONST
  MaxBaby = 1048576;                                   (* 2^20 baby steps cover m <= 2^40 *)

TYPE
  Entry = RECORD v, j: LONGCARD END;
  Table = POINTER TO ARRAY [0..MaxBaby - 1] OF Entry;

PROCEDURE ExtGcd (a, b: LONGINT; VAR x, y: LONGINT) : LONGINT;
VAR
  r0, r1, s0, s1, t0, t1, q, tmp: LONGINT;
BEGIN
  r0 := a; r1 := b; s0 := 1; s1 := 0; t0 := 0; t1 := 1;
  WHILE r1 # 0 DO
    q := Trunc(r0, r1);                 (* truncating quotient, independent of DIV's convention *)
    tmp := r0 - q * r1; r0 := r1; r1 := tmp;
    tmp := s0 - q * s1; s0 := s1; s1 := tmp;
    tmp := t0 - q * t1; t0 := t1; t1 := tmp
  END;
  IF r0 < 0 THEN r0 := -r0; s0 := -s0; t0 := -t0 END;
  x := s0; y := t0;
  RETURN r0
END ExtGcd;

PROCEDURE Trunc (a, b: LONGINT) : LONGINT;
(* quotient rounded toward zero, independent of the dialect's DIV convention *)
VAR
  ua, ub, q: LONGCARD;
BEGIN
  IF a < 0 THEN ua := VAL(LONGCARD, -(a + 1)) + 1 ELSE ua := VAL(LONGCARD, a) END;
  IF b < 0 THEN ub := VAL(LONGCARD, -(b + 1)) + 1 ELSE ub := VAL(LONGCARD, b) END;
  q := ua DIV ub;
  IF (a < 0) # (b < 0) THEN RETURN -VAL(LONGINT, q) END;
  RETURN VAL(LONGINT, q)
END Trunc;

PROCEDURE SubMod (a, b, m: LONGCARD) : LONGCARD;
VAR
  x, y: LONGCARD;
BEGIN
  x := a MOD m; y := b MOD m;
  IF x >= y THEN RETURN x - y END;
  RETURN m - (y - x)
END SubMod;

PROCEDURE NegMod (a, m: LONGCARD) : LONGCARD;
BEGIN
  RETURN SubMod(0, a, m)
END NegMod;

PROCEDURE Inverse (a, m: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
(* Euclid on (m, a mod m) tracking only the coefficient of a, reduced mod m. *)
VAR
  r0, r1, t0, t1, q, tmp: LONGCARD;
BEGIN
  IF m = 0 THEN RETURN FALSE END;
  IF m = 1 THEN r := 0; RETURN TRUE END;
  r0 := m; r1 := a MOD m; t0 := 0; t1 := 1;
  WHILE r1 # 0 DO
    q := r0 DIV r1;
    tmp := r0 - q * r1; r0 := r1; r1 := tmp;
    tmp := SubMod(t0, MulMod(q, t1, m), m); t0 := t1; t1 := tmp
  END;
  IF r0 # 1 THEN RETURN FALSE END;
  r := t0; RETURN TRUE
END Inverse;

PROCEDURE Crt (a1, m1, a2, m2: LONGCARD; VAR x, m: LONGCARD) : BOOLEAN;
VAR
  g, m2g, d, inv, k, l, r1: LONGCARD;
BEGIN
  IF (m1 = 0) OR (m2 = 0) THEN RETURN FALSE END;
  g := Gcd(m1, m2);
  m2g := m2 DIV g;
  IF NOT NatArith.Mul(m1, m2g, l) THEN RETURN FALSE END;
  r1 := a1 MOD m1;
  d := SubMod(a2, r1, m2);
  IF d MOD g # 0 THEN RETURN FALSE END;
  IF m2g = 1 THEN x := r1; m := l; RETURN TRUE END;
  IF NOT Inverse((m1 DIV g) MOD m2g, m2g, inv) THEN RETURN FALSE END;   (* unreachable: coprime *)
  k := MulMod((d DIV g) MOD m2g, inv, m2g);
  x := r1 + m1 * k;                                   (* < m1 + m1 (m2g - 1) = l *)
  m := l;
  RETURN TRUE
END Crt;

PROCEDURE IsPrime (n: LONGCARD) : BOOLEAN;
CONST
  NB = 12;
VAR
  bases: ARRAY [0..NB - 1] OF LONGCARD;
  d, x, a: LONGCARD; s, r, i: CARDINAL; composite: BOOLEAN;
BEGIN
  bases[0] := 2; bases[1] := 3; bases[2] := 5; bases[3] := 7; bases[4] := 11; bases[5] := 13;
  bases[6] := 17; bases[7] := 19; bases[8] := 23; bases[9] := 29; bases[10] := 31; bases[11] := 37;
  IF n < 2 THEN RETURN FALSE END;
  FOR i := 0 TO NB - 1 DO
    IF n = bases[i] THEN RETURN TRUE END;
    IF n MOD bases[i] = 0 THEN RETURN FALSE END
  END;
  d := n - 1; s := 0;
  WHILE NOT ODD(d) DO d := d DIV 2; INC(s) END;
  FOR i := 0 TO NB - 1 DO
    a := bases[i];
    x := PowMod(a, d, n);
    IF (x # 1) AND (x # n - 1) THEN
      composite := TRUE; r := 1;
      WHILE (r < s) AND composite DO
        x := MulMod(x, x, n);
        IF x = n - 1 THEN composite := FALSE END;
        INC(r)
      END;
      IF composite THEN RETURN FALSE END
    END
  END;
  RETURN TRUE
END IsPrime;

PROCEDURE PollardRho (n: LONGCARD) : LONGCARD;
(* Brent's cycle detection with batched gcds; retries with a new constant on failure. *)
VAR
  c, y, x, ys, q, g, r, k, i, lim, diff: LONGCARD;
BEGIN
  IF n <= 3 THEN RETURN n END;
  IF NOT ODD(n) THEN RETURN 2 END;
  IF IsPrime(n) THEN RETURN n END;
  c := 1;
  LOOP
    y := 2; r := 1; q := 1; g := 1; x := y; ys := y;
    WHILE g = 1 DO
      x := y;
      FOR i := 1 TO r DO y := AddMod(MulMod(y, y, n), c, n) END;
      k := 0;
      WHILE (k < r) AND (g = 1) DO
        ys := y;
        IF r - k < 128 THEN lim := r - k ELSE lim := 128 END;
        FOR i := 1 TO lim DO
          y := AddMod(MulMod(y, y, n), c, n);
          IF x > y THEN diff := x - y ELSE diff := y - x END;
          q := MulMod(q, diff, n)
        END;
        g := Gcd(q, n);
        k := k + lim
      END;
      r := r * 2
    END;
    IF g = n THEN                                   (* batch overshot: step back one at a time *)
      REPEAT
        ys := AddMod(MulMod(ys, ys, n), c, n);
        IF x > ys THEN diff := x - ys ELSE diff := ys - x END;
        g := Gcd(diff, n)
      UNTIL g > 1
    END;
    IF (g # n) AND (g > 1) THEN RETURN g END;
    INC(c)
  END
END PollardRho;

PROCEDURE AddFactor (VAR f: Factored; p: LONGCARD; e: CARDINAL);
VAR
  i, j: CARDINAL;
BEGIN
  i := 0;
  WHILE (i < f.count) AND (f.p[i] < p) DO INC(i) END;
  IF (i < f.count) AND (f.p[i] = p) THEN INC(f.e[i], e); RETURN END;
  j := f.count;
  WHILE j > i DO f.p[j] := f.p[j - 1]; f.e[j] := f.e[j - 1]; DEC(j) END;
  f.p[i] := p; f.e[i] := e; INC(f.count)
END AddFactor;

PROCEDURE Split (n: LONGCARD; VAR f: Factored);
VAR
  d: LONGCARD;
BEGIN
  IF n = 1 THEN RETURN END;
  IF IsPrime(n) THEN AddFactor(f, n, 1); RETURN END;
  d := PollardRho(n);
  Split(d, f);
  Split(n DIV d, f)
END Split;

PROCEDURE Factor (n: LONGCARD; VAR f: Factored);
VAR
  m, p: LONGCARD; e: CARDINAL;
BEGIN
  f.count := 0;
  IF n <= 1 THEN RETURN END;
  m := n; p := 2;
  WHILE (p < 1000) AND (p <= m DIV p) DO           (* strip small primes cheaply *)
    IF m MOD p = 0 THEN
      e := 0;
      WHILE m MOD p = 0 DO m := m DIV p; INC(e) END;
      AddFactor(f, p, e)
    END;
    IF p = 2 THEN p := 3 ELSE p := p + 2 END
  END;
  Split(m, f)
END Factor;

PROCEDURE MinFacFast (n: LONGCARD) : LONGCARD;
VAR
  f: Factored;
BEGIN
  IF n = 0 THEN RETURN 2 END;
  IF n = 1 THEN RETURN 1 END;
  Factor(n, f);
  RETURN f.p[0]
END MinFacFast;

PROCEDURE Totient (VAR f: Factored) : LONGCARD;
VAR
  i, j: CARDINAL; r: LONGCARD;
BEGIN
  r := 1;
  FOR i := 0 TO f.count - 1 DO
    r := r * (f.p[i] - 1);
    FOR j := 2 TO f.e[i] DO r := r * f.p[i] END
  END;
  RETURN r
END Totient;

PROCEDURE Order (a, m: LONGCARD) : LONGCARD;
(* order divides λ(m): start from λ(m) and strip prime factors while a^(k/p) = 1 *)
VAR
  k: LONGCARD; f: Factored; i: CARDINAL;
BEGIN
  IF m = 0 THEN RETURN 0 END;
  IF m = 1 THEN RETURN 1 END;
  IF Gcd(a MOD m, m) # 1 THEN RETURN 0 END;
  IF NOT CarmichaelLambda(m, k) THEN RETURN 0 END;
  Factor(k, f);
  IF f.count > 0 THEN
    FOR i := 0 TO f.count - 1 DO
      WHILE (k MOD f.p[i] = 0) AND (PowMod(a, k DIV f.p[i], m) = 1) DO
        k := k DIV f.p[i]
      END
    END
  END;
  RETURN k
END Order;

PROCEDURE CarmichaelLambda (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  f: Factored; i, j: CARDINAL; l, pk: LONGCARD;
BEGIN
  IF n = 0 THEN r := 0; RETURN TRUE END;
  Factor(n, f);
  r := 1;
  IF f.count = 0 THEN RETURN TRUE END;
  FOR i := 0 TO f.count - 1 DO
    pk := f.p[i] - 1;                                  (* φ(p^e) = (p-1) p^(e-1) *)
    FOR j := 2 TO f.e[i] DO pk := pk * f.p[i] END;
    IF (f.p[i] = 2) AND (f.e[i] >= 3) THEN pk := pk DIV 2 END;
    IF NOT NumberTheory.Lcm(r, pk, l) THEN RETURN FALSE END;
    r := l
  END;
  RETURN TRUE
END CarmichaelLambda;

PROCEDURE PrimitiveRoot (m: LONGCARD; VAR g: LONGCARD) : BOOLEAN;
VAR
  f, tf: Factored; phi, c: LONGCARD; i: CARDINAL; ok: BOOLEAN;
BEGIN
  IF m = 0 THEN RETURN FALSE END;
  IF m = 1 THEN g := 0; RETURN TRUE END;
  IF m = 2 THEN g := 1; RETURN TRUE END;
  IF m = 4 THEN g := 3; RETURN TRUE END;
  Factor(m, f);
  (* cyclic iff m = p^k or 2 p^k with p odd *)
  IF NOT ((f.count = 1) AND (f.p[0] # 2) OR (f.count = 2) AND (f.p[0] = 2) AND (f.e[0] = 1)) THEN
    RETURN FALSE
  END;
  phi := Totient(f);
  Factor(phi, tf);
  c := 2;
  WHILE c < m DO
    IF Gcd(c, m) = 1 THEN
      ok := TRUE; i := 0;
      WHILE ok AND (i < tf.count) DO
        IF PowMod(c, phi DIV tf.p[i], m) = 1 THEN ok := FALSE END;
        INC(i)
      END;
      IF ok THEN g := c; RETURN TRUE END
    END;
    INC(c)
  END;
  RETURN FALSE
END PrimitiveRoot;

PROCEDURE SqrtModPrime (a, p: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, q, z, c, t, b, s, mm, i, j, tt: LONGCARD;
BEGIN
  IF NOT IsPrime(p) THEN RETURN FALSE END;
  x := a MOD p;
  IF x = 0 THEN r := 0; RETURN TRUE END;
  IF p = 2 THEN r := 1; RETURN TRUE END;
  IF PowMod(x, (p - 1) DIV 2, p) # 1 THEN RETURN FALSE END;
  q := p - 1; s := 0;
  WHILE NOT ODD(q) DO q := q DIV 2; INC(s) END;
  z := 2;
  WHILE PowMod(z, (p - 1) DIV 2, p) # p - 1 DO INC(z) END;
  mm := s; c := PowMod(z, q, p); t := PowMod(x, q, p); r := PowMod(x, (q + 1) DIV 2, p);
  WHILE t # 1 DO
    i := 0; tt := t;                                   (* least i with t^(2^i) = 1; 0 < i < mm *)
    WHILE tt # 1 DO tt := MulMod(tt, tt, p); INC(i) END;
    b := c; j := mm - i - 1;                           (* b = c^(2^(mm - i - 1)) *)
    WHILE j > 0 DO b := MulMod(b, b, p); DEC(j) END;
    mm := i;
    c := MulMod(b, b, p); t := MulMod(t, c, p); r := MulMod(r, b, p)
  END;
  IF r > p - r THEN r := p - r END;                   (* least root *)
  RETURN TRUE
END SqrtModPrime;

PROCEDURE DiscreteLog (g, h, m: LONGCARD; VAR k: LONGCARD) : BOOLEAN;
VAR
  table: Table;
  n, j, cur, giant, step, target, i, lo, hi, mid: LONGCARD;
BEGIN
  IF (m = 0) OR (m > 1099511627776) THEN RETURN FALSE END;
  IF m = 1 THEN k := 0; RETURN TRUE END;
  target := h MOD m;
  (* small exponents first so the least k is found even when g is not invertible *)
  cur := 1 MOD m;
  FOR j := 0 TO 63 DO
    IF cur = target THEN k := j; RETURN TRUE END;
    cur := MulMod(cur, g, m)
  END;
  IF Gcd(g MOD m, m) # 1 THEN
    (* g^j for j ≥ 64 lies in a cycle whose elements are all already multiples of the
       non-unit part; fall back to a bounded linear scan of one full period *)
    i := 64;
    WHILE i < 64 + m DO
      IF cur = target THEN k := i; RETURN TRUE END;
      cur := MulMod(cur, g, m); INC(i)
    END;
    RETURN FALSE
  END;
  n := NatArith.Sqrt(m) + 1;
  NEW(table);
  IF table = NIL THEN RETURN FALSE END;
  cur := 1 MOD m;
  FOR j := 0 TO n - 1 DO
    table^[j].v := cur; table^[j].j := j;
    cur := MulMod(cur, g, m)
  END;
  SortEntries(table, n);
  IF NOT Inverse(PowMod(g, n, m), m, step) THEN DISPOSE(table); RETURN FALSE END;
  giant := target;
  FOR i := 0 TO n DO
    lo := 0; hi := n;
    WHILE lo < hi DO
      mid := (lo + hi) DIV 2;
      IF table^[mid].v < giant THEN lo := mid + 1 ELSE hi := mid END
    END;
    IF (lo < n) AND (table^[lo].v = giant) THEN
      (* entries with equal v are sorted by j, so lo has the least j *)
      k := i * n + table^[lo].j;
      DISPOSE(table);
      RETURN TRUE
    END;
    giant := MulMod(giant, step, m)
  END;
  DISPOSE(table);
  RETURN FALSE
END DiscreteLog;

PROCEDURE Less (VAR a, b: Entry) : BOOLEAN;
BEGIN
  RETURN (a.v < b.v) OR (a.v = b.v) AND (a.j < b.j)
END Less;

PROCEDURE SortEntries (t: Table; n: LONGCARD);
(* heapsort on (v, j), ascending *)
VAR
  start, end, root, child: LONGCARD; tmp: Entry;
BEGIN
  IF n < 2 THEN RETURN END;
  start := n DIV 2;
  end := n;
  LOOP
    IF start > 0 THEN
      DEC(start)
    ELSE
      DEC(end);
      IF end = 0 THEN EXIT END;
      tmp := t^[end]; t^[end] := t^[0]; t^[0] := tmp
    END;
    root := start;
    LOOP
      child := 2 * root + 1;
      IF child >= end THEN EXIT END;
      IF (child + 1 < end) AND Less(t^[child], t^[child + 1]) THEN INC(child) END;
      IF Less(t^[root], t^[child]) THEN
        tmp := t^[root]; t^[root] := t^[child]; t^[child] := tmp;
        root := child
      ELSE
        EXIT
      END
    END
  END
END SortEntries;

END ModArith.
