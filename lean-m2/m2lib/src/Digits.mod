(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE Digits;

IMPORT NatArith;

PROCEDURE ToDigits (b, n: LONGCARD; VAR l: List) : BOOLEAN;
VAR
  m: LONGCARD; i: CARDINAL;
BEGIN
  l.len := 0;
  IF n = 0 THEN RETURN TRUE END;
  IF b = 0 THEN l.d[0] := n; l.len := 1; RETURN TRUE END;
  IF b = 1 THEN
    IF n > MaxLen THEN RETURN FALSE END;
    i := 0;
    WHILE VAL(LONGCARD, i) < n DO l.d[i] := 1; INC(i) END;
    l.len := i; RETURN TRUE
  END;
  m := n;
  WHILE m > 0 DO
    l.d[l.len] := m MOD b; INC(l.len);
    m := m DIV b
  END;
  RETURN TRUE
END ToDigits;

PROCEDURE OfDigits (b: LONGCARD; VAR l: List; VAR r: LONGCARD) : BOOLEAN;
(* Horner from the most significant digit: ofDigits b (h :: t) = h + b * ofDigits b t *)
VAR
  acc: LONGCARD; i: CARDINAL;
BEGIN
  acc := 0; i := l.len;
  WHILE i > 0 DO
    IF NOT NatArith.Mul(acc, b, acc) THEN RETURN FALSE END;
    IF NOT NatArith.Add(acc, l.d[i - 1], acc) THEN RETURN FALSE END;
    DEC(i)
  END;
  r := acc; RETURN TRUE
END OfDigits;

PROCEDURE Length (b, n: LONGCARD) : LONGCARD;
VAR
  k, m: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  IF b = 0 THEN RETURN 1 END;
  IF b = 1 THEN RETURN n END;
  k := 0; m := n;
  WHILE m > 0 DO m := m DIV b; INC(k) END;
  RETURN k
END Length;

PROCEDURE Sum (b, n: LONGCARD) : LONGCARD;
VAR
  s, m: LONGCARD;
BEGIN
  IF b <= 1 THEN RETURN n END;                 (* [n] or n ones: the sum is n *)
  s := 0; m := n;
  WHILE m > 0 DO s := s + m MOD b; m := m DIV b END;
  RETURN s
END Sum;

PROCEDURE At (b, n, k: LONGCARD) : LONGCARD;
VAR
  m, j: LONGCARD;
BEGIN
  IF b = 0 THEN
    IF (k = 0) THEN RETURN n END;
    RETURN 0
  END;
  IF b = 1 THEN
    IF k < n THEN RETURN 1 END;
    RETURN 0
  END;
  m := n; j := k;
  WHILE (j > 0) AND (m > 0) DO m := m DIV b; DEC(j) END;
  RETURN m MOD b
END At;

PROCEDURE Count (b, n, d: LONGCARD) : LONGCARD;
VAR
  c, m: LONGCARD;
BEGIN
  IF n = 0 THEN RETURN 0 END;
  IF b = 0 THEN
    IF d = n THEN RETURN 1 END;
    RETURN 0
  END;
  IF b = 1 THEN
    IF d = 1 THEN RETURN n END;
    RETURN 0
  END;
  c := 0; m := n;
  WHILE m > 0 DO
    IF m MOD b = d THEN INC(c) END;
    m := m DIV b
  END;
  RETURN c
END Count;

PROCEDURE Reverse (b, n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, m: LONGCARD;
BEGIN
  IF b <= 1 THEN r := n; RETURN TRUE END;      (* [n] and 1…1 are their own reversals *)
  acc := 0; m := n;
  WHILE m > 0 DO
    IF NOT NatArith.Mul(acc, b, acc) THEN RETURN FALSE END;
    IF NOT NatArith.Add(acc, m MOD b, acc) THEN RETURN FALSE END;
    m := m DIV b
  END;
  r := acc; RETURN TRUE
END Reverse;

PROCEDURE IsPalindrome (b, n: LONGCARD) : BOOLEAN;
VAR
  l: List; i, j: CARDINAL;
BEGIN
  IF b <= 1 THEN RETURN TRUE END;
  IF NOT ToDigits(b, n, l) THEN RETURN FALSE END;
  IF l.len = 0 THEN RETURN TRUE END;
  i := 0; j := l.len - 1;
  WHILE i < j DO
    IF l.d[i] # l.d[j] THEN RETURN FALSE END;
    INC(i); DEC(j)
  END;
  RETURN TRUE
END IsPalindrome;

PROCEDURE Product (b, n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  p, m: LONGCARD;
BEGIN
  IF n = 0 THEN r := 1; RETURN TRUE END;       (* empty product *)
  IF b = 0 THEN r := n; RETURN TRUE END;
  IF b = 1 THEN r := 1; RETURN TRUE END;
  p := 1; m := n;
  WHILE m > 0 DO
    IF NOT NatArith.Mul(p, m MOD b, p) THEN RETURN FALSE END;
    m := m DIV b
  END;
  r := p; RETURN TRUE
END Product;

PROCEDURE AllDistinct (b, n: LONGCARD) : BOOLEAN;
VAR
  l: List; i, j: CARDINAL;
BEGIN
  IF b = 1 THEN RETURN n <= 1 END;
  IF NOT ToDigits(b, n, l) THEN RETURN FALSE END;
  i := 0;
  WHILE i < l.len DO
    j := i + 1;
    WHILE j < l.len DO
      IF l.d[i] = l.d[j] THEN RETURN FALSE END;
      INC(j)
    END;
    INC(i)
  END;
  RETURN TRUE
END AllDistinct;

PROCEDURE ContainsDigit (b, n, d: LONGCARD) : BOOLEAN;
BEGIN
  RETURN Count(b, n, d) > 0
END ContainsDigit;

PROCEDURE Concat (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  p, t: LONGCARD;
BEGIN
  IF NOT NatArith.Pow(10, Length(10, b), p) THEN RETURN FALSE END;
  IF NOT NatArith.Mul(a, p, t) THEN RETURN FALSE END;
  RETURN NatArith.Add(t, b, r)
END Concat;

PROCEDURE Bits (n: LONGCARD; VAR l: List);
VAR
  m: LONGCARD;
BEGIN
  l.len := 0; m := n;
  WHILE m > 0 DO
    l.d[l.len] := m MOD 2; INC(l.len);
    m := m DIV 2
  END
END Bits;

END Digits.
