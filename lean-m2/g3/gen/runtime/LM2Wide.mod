(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE LM2Wide;
(* Same algorithms as lm2_wide.h (Knuth, TAOCP vol. 2, 4.3.1, Algorithm D for division). *)

IMPORT LM2Nat;

CONST
  Base = 100000000H;         (* 2^32 *)
  Bits = Limbs * 32;

TYPE
  Buf = ARRAY [0..Limbs] OF CARDINAL;

PROCEDURE Norm (VAR a: Wide);
BEGIN
  WHILE (a.n > 0) AND (a.d[a.n - 1] = 0) DO DEC(a.n) END
END Norm;

PROCEDURE Set (VAR r: Wide; x: LONGCARD);
BEGIN
  r.d[0] := VAL(CARDINAL, x MOD Base);
  r.d[1] := VAL(CARDINAL, x DIV Base);
  r.n := 2; Norm(r)
END Set;

PROCEDURE Get (VAR a: Wide; VAR x: LONGCARD) : BOOLEAN;
BEGIN
  IF a.n > 2 THEN RETURN TRUE END;
  x := 0;
  IF a.n > 0 THEN x := VAL(LONGCARD, a.d[0]) END;
  IF a.n > 1 THEN x := x + VAL(LONGCARD, a.d[1]) * Base END;
  RETURN FALSE
END Get;

PROCEDURE IsZero (VAR a: Wide) : BOOLEAN;
BEGIN
  RETURN a.n = 0
END IsZero;

PROCEDURE Cmp (VAR a, b: Wide) : INTEGER;
VAR
  i: CARDINAL;
BEGIN
  IF a.n # b.n THEN
    IF a.n < b.n THEN RETURN -1 ELSE RETURN 1 END
  END;
  i := a.n;
  WHILE i > 0 DO
    IF a.d[i - 1] # b.d[i - 1] THEN
      IF a.d[i - 1] < b.d[i - 1] THEN RETURN -1 ELSE RETURN 1 END
    END;
    DEC(i)
  END;
  RETURN 0
END Cmp;

PROCEDURE BitLen (VAR a: Wide) : CARDINAL;
VAR
  top, k: CARDINAL;
BEGIN
  IF a.n = 0 THEN RETURN 0 END;
  top := a.d[a.n - 1]; k := 0;
  WHILE top # 0 DO top := top DIV 2; INC(k) END;
  RETURN (a.n - 1) * 32 + k
END BitLen;

PROCEDURE Limb (VAR a: Wide; i: CARDINAL) : LONGCARD;
BEGIN
  IF i < a.n THEN RETURN VAL(LONGCARD, a.d[i]) ELSE RETURN 0 END
END Limb;

PROCEDURE Add (VAR a, b, r: Wide) : BOOLEAN;
VAR
  t: Wide; i, m: CARDINAL; c: LONGCARD;
BEGIN
  IF a.n > b.n THEN m := a.n ELSE m := b.n END;
  c := 0; i := 0;
  WHILE i < m DO
    c := c + Limb(a, i) + Limb(b, i);
    t.d[i] := VAL(CARDINAL, c MOD Base); c := c DIV Base;
    INC(i)
  END;
  IF c # 0 THEN
    IF m = Limbs THEN RETURN TRUE END;
    t.d[m] := VAL(CARDINAL, c); INC(m)
  END;
  t.n := m; r := t; RETURN FALSE
END Add;

PROCEDURE Sub (VAR a, b, r: Wide) : BOOLEAN;
VAR
  t: Wide; i: CARDINAL; c: LONGINT;
BEGIN
  IF Cmp(a, b) <= 0 THEN r.n := 0; RETURN FALSE END;
  c := 0; i := 0;
  WHILE i < a.n DO
    c := c + VAL(LONGINT, Limb(a, i)) - VAL(LONGINT, Limb(b, i));
    IF c < 0 THEN
      t.d[i] := VAL(CARDINAL, c + VAL(LONGINT, Base)); c := -1
    ELSE
      t.d[i] := VAL(CARDINAL, c); c := 0
    END;
    INC(i)
  END;
  t.n := a.n; Norm(t); r := t; RETURN FALSE
END Sub;

PROCEDURE Mul (VAR a, b, r: Wide) : BOOLEAN;
VAR
  buf: Buf; i, j, m: CARDINAL; c, p: LONGCARD;
BEGIN
  IF (a.n = 0) OR (b.n = 0) THEN r.n := 0; RETURN FALSE END;
  m := a.n + b.n;                                     (* the product has m - 1 or m limbs *)
  IF m - 1 > Limbs THEN RETURN TRUE END;
  i := 0; WHILE i < m DO buf[i] := 0; INC(i) END;
  i := 0;
  WHILE i < a.n DO
    c := 0; j := 0;
    WHILE j < b.n DO
      p := VAL(LONGCARD, a.d[i]) * VAL(LONGCARD, b.d[j]) + VAL(LONGCARD, buf[i + j]) + c;
      buf[i + j] := VAL(CARDINAL, p MOD Base); c := p DIV Base;
      INC(j)
    END;
    buf[i + b.n] := VAL(CARDINAL, c);
    INC(i)
  END;
  WHILE (m > 0) AND (buf[m - 1] = 0) DO DEC(m) END;
  IF m > Limbs THEN RETURN TRUE END;
  i := 0; WHILE i < m DO r.d[i] := buf[i]; INC(i) END;
  r.n := m; RETURN FALSE
END Mul;

PROCEDURE P2 (s: CARDINAL) : LONGCARD;     (* 2^s, s < 64 *)
VAR
  v: LONGCARD;
BEGIN
  v := 1; WHILE s > 0 DO v := v * 2; DEC(s) END; RETURN v
END P2;

PROCEDURE Shl (x, s: CARDINAL) : CARDINAL;  (* (x << s) mod 2^32 *)
BEGIN
  RETURN VAL(CARDINAL, (VAL(LONGCARD, x) * P2(s)) MOD Base)
END Shl;

PROCEDURE Shr (x, s: CARDINAL) : CARDINAL;  (* x >> s, s <= 32 *)
BEGIN
  RETURN VAL(CARDINAL, VAL(LONGCARD, x) DIV P2(s))
END Shr;

PROCEDURE FDiv32 (t: LONGINT) : LONGINT;    (* floor(t / 2^32) *)
BEGIN
  IF t >= 0 THEN RETURN t DIV VAL(LONGINT, Base)
  ELSE RETURN -((-(t + 1)) DIV VAL(LONGINT, Base)) - 1 END
END FDiv32;

PROCEDURE DivMod (VAR a, b, q, rem: Wide);   (* b # 0 *)
VAR
  qq, rr: Wide; un, vn: Buf;
  m, n, s, i, top, v: CARDINAL; j: INTEGER;
  k64, cur, num, qhat, rhat, p, c: LONGCARD;
  t, k: LONGINT;
BEGIN
  IF Cmp(a, b) < 0 THEN rr := a; qq.n := 0; q := qq; rem := rr; RETURN END;
  m := a.n; n := b.n;
  IF n = 1 THEN
    k64 := 0; v := b.d[0]; i := m;
    WHILE i > 0 DO
      cur := k64 * Base + VAL(LONGCARD, a.d[i - 1]);
      qq.d[i - 1] := VAL(CARDINAL, cur DIV VAL(LONGCARD, v)); k64 := cur MOD VAL(LONGCARD, v);
      DEC(i)
    END;
    qq.n := m; Norm(qq); Set(rr, k64); q := qq; rem := rr; RETURN
  END;
  s := 0; top := b.d[n - 1];
  WHILE top < 80000000H DO top := top * 2; INC(s) END;
  i := n - 1;
  WHILE i > 0 DO
    IF s > 0 THEN vn[i] := Shl(b.d[i], s) + Shr(b.d[i - 1], 32 - s) ELSE vn[i] := b.d[i] END;
    DEC(i)
  END;
  vn[0] := Shl(b.d[0], s);
  IF s > 0 THEN un[m] := Shr(a.d[m - 1], 32 - s) ELSE un[m] := 0 END;
  i := m - 1;
  WHILE i > 0 DO
    IF s > 0 THEN un[i] := Shl(a.d[i], s) + Shr(a.d[i - 1], 32 - s) ELSE un[i] := a.d[i] END;
    DEC(i)
  END;
  un[0] := Shl(a.d[0], s);
  j := VAL(INTEGER, m - n);
  WHILE j >= 0 DO
    num := VAL(LONGCARD, un[VAL(CARDINAL, j) + n]) * Base + VAL(LONGCARD, un[VAL(CARDINAL, j) + n - 1]);
    qhat := num DIV VAL(LONGCARD, vn[n - 1]); rhat := num MOD VAL(LONGCARD, vn[n - 1]);
    LOOP
      IF (qhat < Base) AND
         (qhat * VAL(LONGCARD, vn[n - 2]) <= rhat * Base + VAL(LONGCARD, un[VAL(CARDINAL, j) + n - 2])) THEN
        EXIT
      END;
      DEC(qhat); rhat := rhat + VAL(LONGCARD, vn[n - 1]);
      IF rhat >= Base THEN EXIT END
    END;
    k := 0; i := 0;
    WHILE i < n DO
      p := qhat * VAL(LONGCARD, vn[i]);
      t := VAL(LONGINT, un[i + VAL(CARDINAL, j)]) - k - VAL(LONGINT, p MOD Base);
      IF t < 0 THEN un[i + VAL(CARDINAL, j)] := VAL(CARDINAL, t - FDiv32(t) * VAL(LONGINT, Base))
      ELSE un[i + VAL(CARDINAL, j)] := VAL(CARDINAL, t MOD VAL(LONGINT, Base)) END;
      k := VAL(LONGINT, p DIV Base) - FDiv32(t);
      INC(i)
    END;
    t := VAL(LONGINT, un[VAL(CARDINAL, j) + n]) - k;
    IF t < 0 THEN un[VAL(CARDINAL, j) + n] := VAL(CARDINAL, t - FDiv32(t) * VAL(LONGINT, Base))
    ELSE un[VAL(CARDINAL, j) + n] := VAL(CARDINAL, t MOD VAL(LONGINT, Base)) END;
    qq.d[VAL(CARDINAL, j)] := VAL(CARDINAL, qhat);
    IF t < 0 THEN
      qq.d[VAL(CARDINAL, j)] := qq.d[VAL(CARDINAL, j)] - 1;
      c := 0; i := 0;
      WHILE i < n DO
        c := c + VAL(LONGCARD, un[i + VAL(CARDINAL, j)]) + VAL(LONGCARD, vn[i]);
        un[i + VAL(CARDINAL, j)] := VAL(CARDINAL, c MOD Base); c := c DIV Base;
        INC(i)
      END;
      un[VAL(CARDINAL, j) + n] := VAL(CARDINAL, (VAL(LONGCARD, un[VAL(CARDINAL, j) + n]) + c) MOD Base)
    END;
    DEC(j)
  END;
  qq.n := m - n + 1; Norm(qq);
  i := 0;
  WHILE i < n DO
    IF s > 0 THEN rr.d[i] := Shr(un[i], s) + Shl(un[i + 1], 32 - s) ELSE rr.d[i] := un[i] END;
    INC(i)
  END;
  rr.n := n; Norm(rr);
  q := qq; rem := rr
END DivMod;

PROCEDURE Div (VAR a, b, r: Wide) : BOOLEAN;
VAR
  q, m: Wide;
BEGIN
  IF b.n = 0 THEN r.n := 0; RETURN FALSE END;
  DivMod(a, b, q, m); r := q; RETURN FALSE
END Div;

PROCEDURE Mod (VAR a, b, r: Wide) : BOOLEAN;
VAR
  q, m: Wide;
BEGIN
  IF b.n = 0 THEN r := a; RETURN FALSE END;
  DivMod(a, b, q, m); r := m; RETURN FALSE
END Mod;

PROCEDURE Pow (VAR a, e, r: Wide) : BOOLEAN;
VAR
  acc, base, one: Wide; k: LONGCARD;
BEGIN
  IF e.n = 0 THEN Set(r, 1); RETURN FALSE END;
  Set(one, 1);
  IF (a.n = 0) OR (Cmp(a, one) = 0) THEN r := a; RETURN FALSE END;
  IF Get(e, k) OR (k > VAL(LONGCARD, Bits)) THEN RETURN TRUE END;
  acc := one; base := a;
  LOOP
    IF ODD(k) THEN
      IF Mul(acc, base, acc) THEN RETURN TRUE END
    END;
    k := k DIV 2;
    IF k = 0 THEN EXIT END;
    IF Mul(base, base, base) THEN RETURN TRUE END
  END;
  r := acc; RETURN FALSE
END Pow;

PROCEDURE Min (VAR a, b, r: Wide) : BOOLEAN;
BEGIN
  IF Cmp(a, b) <= 0 THEN r := a ELSE r := b END; RETURN FALSE
END Min;

PROCEDURE Max (VAR a, b, r: Wide) : BOOLEAN;
BEGIN
  IF Cmp(a, b) >= 0 THEN r := a ELSE r := b END; RETURN FALSE
END Max;

PROCEDURE Gcd (VAR a, b, r: Wide) : BOOLEAN;
VAR
  x, y, t: Wide;
BEGIN
  x := a; y := b;
  WHILE y.n # 0 DO
    IF Mod(x, y, t) THEN END;
    x := y; y := t
  END;
  r := x; RETURN FALSE
END Gcd;

PROCEDURE Lcm (VAR a, b, r: Wide) : BOOLEAN;
VAR
  g, q: Wide;
BEGIN
  IF (a.n = 0) OR (b.n = 0) THEN r.n := 0; RETURN FALSE END;
  IF Gcd(a, b, g) OR Div(a, g, q) THEN END;
  RETURN Mul(q, b, r)
END Lcm;

PROCEDURE Fact (VAR n, r: Wide) : BOOLEAN;
VAR
  acc, iw: Wide; k, i: LONGCARD;
BEGIN
  IF Get(n, k) THEN RETURN TRUE END;
  Set(acc, 1); i := 2;
  WHILE i <= k DO
    Set(iw, i);
    IF Mul(acc, iw, acc) THEN RETURN TRUE END;
    INC(i)
  END;
  r := acc; RETURN FALSE
END Fact;

PROCEDURE Choose (VAR n, k, r: Wide) : BOOLEAN;
VAR
  c, kk, nk, t, iw: Wide; steps, i: LONGCARD;
BEGIN
  IF Cmp(k, n) > 0 THEN r.n := 0; RETURN FALSE END;
  IF Sub(n, k, nk) THEN END;
  IF Cmp(k, nk) <= 0 THEN kk := k ELSE kk := nk END;
  IF Get(kk, steps) THEN RETURN TRUE END;
  IF Sub(n, kk, nk) THEN END;
  Set(c, 1); i := 1;
  WHILE i <= steps DO
    Set(iw, i);
    IF Add(nk, iw, t) THEN RETURN TRUE END;
    IF Mul(c, t, c) THEN RETURN TRUE END;
    IF Div(c, iw, c) THEN END;
    INC(i)
  END;
  r := c; RETURN FALSE
END Choose;

PROCEDURE Sqrt (VAR n, r: Wide) : BOOLEAN;
VAR
  x, y, q, two: Wide; b, i: CARDINAL;
BEGIN
  IF n.n = 0 THEN r.n := 0; RETURN FALSE END;
  b := (BitLen(n) + 1) DIV 2;
  x.n := b DIV 32 + 1;
  i := 0; WHILE i < x.n DO x.d[i] := 0; INC(i) END;
  x.d[b DIV 32] := VAL(CARDINAL, P2(b MOD 32));
  Set(two, 2);
  LOOP
    IF Div(n, x, q) THEN END;
    IF Add(x, q, y) THEN RETURN TRUE END;
    IF Div(y, two, y) THEN END;
    IF Cmp(y, x) >= 0 THEN EXIT END;
    x := y
  END;
  r := x; RETURN FALSE
END Sqrt;

PROCEDURE MinFac (VAR n, r: Wide) : BOOLEAN;
VAR
  x, m: LONGCARD;
BEGIN
  IF Get(n, x) THEN RETURN TRUE END;
  IF LM2Nat.MinFac(x, m) THEN RETURN TRUE END;
  Set(r, m); RETURN FALSE
END MinFac;

PROCEDURE Prime (VAR n, r: Wide) : BOOLEAN;
VAR
  x: LONGCARD;
BEGIN
  IF Get(n, x) THEN RETURN TRUE END;
  Set(r, LM2Nat.IsPrime(x)); RETURN FALSE
END Prime;

PROCEDURE BigOmega (VAR n, r: Wide) : BOOLEAN;
VAR
  x: LONGCARD;
BEGIN
  IF Get(n, x) THEN RETURN TRUE END;
  Set(r, LM2Nat.BigOmega(x)); RETURN FALSE
END BigOmega;

PROCEDURE PfNth (VAR n, k, r: Wide) : BOOLEAN;
VAR
  x, j: LONGCARD;
BEGIN
  IF Get(n, x) THEN RETURN TRUE END;
  IF Get(k, j) THEN Set(r, 0); RETURN FALSE END;   (* k >= 2^64 > Omega(n) *)
  Set(r, LM2Nat.PfNth(x, j)); RETURN FALSE
END PfNth;

PROCEDURE DigAt (VAR b, n, k, r: Wide) : BOOLEAN;
VAR
  bb, m, q, d, one: Wide; j: LONGCARD;
BEGIN
  Set(one, 1);
  IF b.n = 0 THEN
    IF k.n = 0 THEN r := n ELSE Set(r, 0) END;
    RETURN FALSE
  END;
  IF Cmp(b, one) = 0 THEN
    IF Cmp(k, n) < 0 THEN Set(r, 1) ELSE Set(r, 0) END;
    RETURN FALSE
  END;
  IF Get(k, j) THEN Set(r, 0); RETURN FALSE END;   (* k >= 2^64 > bit length of n *)
  bb := b; m := n;
  WHILE (j > 0) AND (m.n # 0) DO DivMod(m, bb, q, d); m := q; DEC(j) END;
  DivMod(m, bb, q, d); r := d; RETURN FALSE
END DigAt;

PROCEDURE Dvd (VAR a, b, r: Wide) : BOOLEAN;
VAR
  m: Wide;
BEGIN
  IF a.n = 0 THEN
    IF b.n = 0 THEN Set(r, 1) ELSE Set(r, 0) END;
    RETURN FALSE
  END;
  IF Mod(b, a, m) THEN END;
  IF m.n = 0 THEN Set(r, 1) ELSE Set(r, 0) END;
  RETURN FALSE
END Dvd;

PROCEDURE Fib (VAR n, r: Wide) : BOOLEAN;
VAR
  x, y, z: Wide; k, i: LONGCARD;
BEGIN
  IF Get(n, k) THEN RETURN TRUE END;
  Set(x, 0); Set(y, 1); i := 0;
  WHILE i < k DO
    IF Add(x, y, z) THEN
      IF i + 1 = k THEN r := y; RETURN FALSE END;
      RETURN TRUE
    END;
    x := y; y := z; INC(i)
  END;
  r := x; RETURN FALSE
END Fib;

PROCEDURE Log (VAR b, n, r: Wide) : BOOLEAN;
VAR
  m, one: Wide; k: LONGCARD;
BEGIN
  Set(one, 1);
  IF Cmp(b, one) <= 0 THEN r.n := 0; RETURN FALSE END;
  m := n; k := 0;
  WHILE Cmp(m, b) >= 0 DO
    IF Div(m, b, m) THEN END;
    INC(k)
  END;
  Set(r, k); RETURN FALSE
END Log;

PROCEDURE Log2 (VAR n, r: Wide) : BOOLEAN;
VAR
  b: CARDINAL;
BEGIN
  b := BitLen(n);
  IF b > 0 THEN Set(r, VAL(LONGCARD, b - 1)) ELSE Set(r, 0) END;
  RETURN FALSE
END Log2;

PROCEDURE Padic (VAR p, n, r: Wide) : BOOLEAN;
VAR
  m, q, rem, one: Wide; k: LONGCARD;
BEGIN
  Set(one, 1);
  IF (Cmp(p, one) <= 0) OR (n.n = 0) THEN r.n := 0; RETURN FALSE END;
  m := n; k := 0;
  LOOP
    DivMod(m, p, q, rem);
    IF rem.n # 0 THEN EXIT END;
    m := q; INC(k)
  END;
  Set(r, k); RETURN FALSE
END Padic;

PROCEDURE DigSum (VAR b, n, r: Wide) : BOOLEAN;
VAR
  m, q, d, s, one: Wide;
BEGIN
  Set(one, 1);
  IF Cmp(b, one) <= 0 THEN r := n; RETURN FALSE END;
  m := n; s.n := 0;
  WHILE m.n # 0 DO
    DivMod(m, b, q, d);
    IF Add(s, d, s) THEN RETURN TRUE END;
    m := q
  END;
  r := s; RETURN FALSE
END DigSum;

PROCEDURE DigLen (VAR b, n, r: Wide) : BOOLEAN;
VAR
  m, q, d, one: Wide; k: LONGCARD;
BEGIN
  Set(one, 1);
  IF b.n = 0 THEN
    IF n.n = 0 THEN Set(r, 0) ELSE Set(r, 1) END;
    RETURN FALSE
  END;
  IF Cmp(b, one) = 0 THEN r := n; RETURN FALSE END;
  m := n; k := 0;
  WHILE m.n # 0 DO DivMod(m, b, q, d); m := q; INC(k) END;
  Set(r, k); RETURN FALSE
END DigLen;

PROCEDURE DigRev (VAR b, n, r: Wide) : BOOLEAN;
VAR
  m, q, d, acc, one: Wide;
BEGIN
  Set(one, 1);
  IF Cmp(b, one) <= 0 THEN r := n; RETURN FALSE END;
  m := n; acc.n := 0;
  WHILE m.n # 0 DO
    DivMod(m, b, q, d);
    IF Mul(acc, b, acc) THEN RETURN TRUE END;
    IF Add(acc, d, acc) THEN RETURN TRUE END;
    m := q
  END;
  r := acc; RETURN FALSE
END DigRev;

PROCEDURE XorLimb (a, b: CARDINAL) : CARDINAL;
VAR
  r, p: LONGCARD; x, y, i: CARDINAL;
BEGIN
  r := 0; p := 1; x := a; y := b; i := 0;
  WHILE i < 32 DO
    IF ODD(x) # ODD(y) THEN r := r + p END;
    x := x DIV 2; y := y DIV 2; p := p * 2; INC(i)
  END;
  RETURN VAL(CARDINAL, r)
END XorLimb;

PROCEDURE Xor (VAR a, b, r: Wide) : BOOLEAN;
VAR
  t: Wide; i, m: CARDINAL;
BEGIN
  IF a.n > b.n THEN m := a.n ELSE m := b.n END;
  i := 0;
  WHILE i < m DO t.d[i] := XorLimb(VAL(CARDINAL, Limb(a, i)), VAL(CARDINAL, Limb(b, i))); INC(i) END;
  t.n := m; Norm(t); r := t; RETURN FALSE
END Xor;

(* ---- ℤ (sign-magnitude) ---- *)

PROCEDURE Fix (VAR a: WInt);
BEGIN
  IF a.m.n = 0 THEN a.neg := FALSE END
END Fix;

PROCEDURE IOfNat (VAR a: Wide; VAR r: WInt) : BOOLEAN;
BEGIN
  r.m := a; r.neg := FALSE; RETURN FALSE
END IOfNat;

PROCEDURE INeg (VAR a, r: WInt) : BOOLEAN;
VAR
  t: WInt;
BEGIN
  t := a; t.neg := NOT t.neg; Fix(t); r := t; RETURN FALSE
END INeg;

PROCEDURE ISign (VAR a, r: WInt) : BOOLEAN;
VAR
  t: WInt;
BEGIN
  IF a.m.n = 0 THEN Set(t.m, 0) ELSE Set(t.m, 1) END;
  t.neg := a.neg; Fix(t); r := t; RETURN FALSE
END ISign;

PROCEDURE IAdd (VAR a, b, r: WInt) : BOOLEAN;
VAR
  t: WInt;
BEGIN
  IF a.neg = b.neg THEN
    IF Add(a.m, b.m, t.m) THEN RETURN TRUE END;
    t.neg := a.neg
  ELSIF Cmp(a.m, b.m) >= 0 THEN
    IF Sub(a.m, b.m, t.m) THEN END;
    t.neg := a.neg
  ELSE
    IF Sub(b.m, a.m, t.m) THEN END;
    t.neg := b.neg
  END;
  Fix(t); r := t; RETURN FALSE
END IAdd;

PROCEDURE ISub (VAR a, b, r: WInt) : BOOLEAN;
VAR
  nb: WInt;
BEGIN
  nb := b; nb.neg := NOT nb.neg; Fix(nb);
  RETURN IAdd(a, nb, r)
END ISub;

PROCEDURE IMul (VAR a, b, r: WInt) : BOOLEAN;
VAR
  t: WInt;
BEGIN
  IF Mul(a.m, b.m, t.m) THEN RETURN TRUE END;
  t.neg := a.neg # b.neg; Fix(t); r := t; RETURN FALSE
END IMul;

PROCEDURE IPow (VAR a: WInt; VAR e: Wide; VAR r: WInt) : BOOLEAN;
VAR
  t: WInt;
BEGIN
  IF Pow(a.m, e, t.m) THEN RETURN TRUE END;
  t.neg := a.neg AND (e.n # 0) AND ODD(e.d[0]); Fix(t); r := t; RETURN FALSE
END IPow;

PROCEDURE IToNat (VAR a: WInt; VAR r: Wide) : BOOLEAN;
BEGIN
  IF a.neg THEN r.n := 0 ELSE r := a.m END; RETURN FALSE
END IToNat;

PROCEDURE INatAbs (VAR a: WInt; VAR r: Wide) : BOOLEAN;
BEGIN
  r := a.m; RETURN FALSE
END INatAbs;

PROCEDURE ICmp (VAR a, b: WInt) : INTEGER;
BEGIN
  IF a.neg # b.neg THEN
    IF a.neg THEN RETURN -1 ELSE RETURN 1 END
  END;
  IF a.neg THEN RETURN -Cmp(a.m, b.m) ELSE RETURN Cmp(a.m, b.m) END
END ICmp;

(* ---- ℚ (MathIR v6) ---- *)

PROCEDURE QNorm (VAR q: WRat) : BOOLEAN;
VAR
  g, one: Wide;
BEGIN
  IF q.den.n = 0 THEN RETURN TRUE END;          (* never produced; fail closed *)
  Set(one, 1);
  IF q.num.m.n = 0 THEN q.num.neg := FALSE; q.den := one; RETURN FALSE END;
  IF Gcd(q.num.m, q.den, g) THEN END;
  IF Cmp(g, one) # 0 THEN
    IF Div(q.num.m, g, q.num.m) OR Div(q.den, g, q.den) THEN END
  END;
  RETURN FALSE
END QNorm;

PROCEDURE QOfNat (VAR a: Wide; VAR r: WRat) : BOOLEAN;
VAR
  t: WRat;
BEGIN
  t.num.m := a; t.num.neg := FALSE; Set(t.den, 1); r := t; RETURN FALSE
END QOfNat;

PROCEDURE QOfInt (VAR a: WInt; VAR r: WRat) : BOOLEAN;
VAR
  t: WRat;
BEGIN
  t.num := a; Set(t.den, 1); r := t; RETURN FALSE
END QOfInt;

PROCEDURE QAdd (VAR a, b, r: WRat) : BOOLEAN;
VAR
  t: WRat; x, y, ad, bd: WInt;
BEGIN
  ad.neg := FALSE; ad.m := a.den; bd.neg := FALSE; bd.m := b.den;
  IF IMul(a.num, bd, x) OR IMul(b.num, ad, y) OR IAdd(x, y, t.num) THEN RETURN TRUE END;
  IF Mul(a.den, b.den, t.den) THEN RETURN TRUE END;
  IF QNorm(t) THEN RETURN TRUE END;
  r := t; RETURN FALSE
END QAdd;

PROCEDURE QNeg (VAR a, r: WRat) : BOOLEAN;
VAR
  t: WRat;
BEGIN
  t := a; t.num.neg := NOT t.num.neg; Fix(t.num); r := t; RETURN FALSE
END QNeg;

PROCEDURE QSub (VAR a, b, r: WRat) : BOOLEAN;
VAR
  nb: WRat;
BEGIN
  IF QNeg(b, nb) THEN END;
  RETURN QAdd(a, nb, r)
END QSub;

PROCEDURE QMul (VAR a, b, r: WRat) : BOOLEAN;
VAR
  t: WRat;
BEGIN
  IF IMul(a.num, b.num, t.num) OR Mul(a.den, b.den, t.den) THEN RETURN TRUE END;
  IF QNorm(t) THEN RETURN TRUE END;
  r := t; RETURN FALSE
END QMul;

PROCEDURE QInv (VAR a, r: WRat) : BOOLEAN;
VAR
  t: WRat; zero: Wide;
BEGIN
  IF a.num.m.n = 0 THEN zero.n := 0; RETURN QOfNat(zero, r) END;
  t.num.m := a.den; t.num.neg := a.num.neg; t.den := a.num.m;   (* already coprime *)
  r := t; RETURN FALSE
END QInv;

PROCEDURE QDiv (VAR a, b, r: WRat) : BOOLEAN;
VAR
  ib: WRat;
BEGIN
  IF QInv(b, ib) THEN END;
  RETURN QMul(a, ib, r)
END QDiv;

PROCEDURE QPow (VAR a: WRat; VAR e: Wide; VAR r: WRat) : BOOLEAN;
VAR
  t: WRat;
BEGIN
  IF IPow(a.num, e, t.num) OR Pow(a.den, e, t.den) THEN RETURN TRUE END;
  r := t; RETURN FALSE                           (* num^e / den^e stays coprime *)
END QPow;

PROCEDURE QNum (VAR a: WRat; VAR r: WInt) : BOOLEAN;
BEGIN
  r := a.num; RETURN FALSE
END QNum;

PROCEDURE QDen (VAR a: WRat; VAR r: Wide) : BOOLEAN;
BEGIN
  r := a.den; RETURN FALSE
END QDen;

END LM2Wide.
