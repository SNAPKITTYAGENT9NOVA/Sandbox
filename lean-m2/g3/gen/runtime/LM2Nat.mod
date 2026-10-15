IMPLEMENTATION MODULE LM2Nat;

CONST
  Top = MAX(LONGCARD);

PROCEDURE Add (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF a > Top - b THEN RETURN TRUE END;
  r := a + b; RETURN FALSE
END Add;

PROCEDURE Mul (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF (a # 0) AND (b > Top DIV a) THEN RETURN TRUE END;
  r := a * b; RETURN FALSE
END Mul;

PROCEDURE Sub (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF a > b THEN r := a - b ELSE r := 0 END;
  RETURN FALSE
END Sub;

PROCEDURE Div (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF b = 0 THEN r := 0 ELSE r := a DIV b END;
  RETURN FALSE
END Div;

PROCEDURE Mod (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
BEGIN
  IF b = 0 THEN r := a ELSE r := a MOD b END;
  RETURN FALSE
END Mod;

PROCEDURE Pow (a, e: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, base, k: LONGCARD;
BEGIN
  IF e = 0 THEN r := 1; RETURN FALSE END;
  IF a = 0 THEN r := 0; RETURN FALSE END;
  IF a = 1 THEN r := 1; RETURN FALSE END;
  IF e >= 64 THEN RETURN TRUE END;
  acc := 1; base := a; k := e;
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

PROCEDURE Min (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a < b THEN RETURN a ELSE RETURN b END
END Min;

PROCEDURE Max (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a < b THEN RETURN b ELSE RETURN a END
END Max;

PROCEDURE Gcd (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, y, t: LONGCARD;
BEGIN
  x := a; y := b;
  WHILE y # 0 DO t := x MOD y; x := y; y := t END;
  r := x; RETURN FALSE
END Gcd;

PROCEDURE Lcm (a, b: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  g: LONGCARD;
BEGIN
  IF (a = 0) OR (b = 0) THEN r := 0; RETURN FALSE END;
  IF Gcd(a, b, g) THEN RETURN TRUE END;
  RETURN Mul(a DIV g, b, r)
END Lcm;

PROCEDURE Fact (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  acc, i: LONGCARD;
BEGIN
  IF n > 20 THEN RETURN TRUE END;
  acc := 1; i := 2;
  WHILE i <= n DO acc := acc * i; INC(i) END;
  r := acc; RETURN FALSE
END Fact;

PROCEDURE Choose (n, k: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  c, i, g, num, den, t, kk: LONGCARD;
BEGIN
  IF k > n THEN r := 0; RETURN FALSE END;
  kk := k;
  IF kk > n - kk THEN kk := n - kk END;
  c := 1; i := 1;
  WHILE i <= kk DO
    num := n - kk + i; den := i;
    IF Gcd(c, den, g) THEN RETURN TRUE END;
    c := c DIV g; den := den DIV g;
    IF Gcd(num, den, g) THEN RETURN TRUE END;
    num := num DIV g;
    IF Mul(c, num, t) THEN RETURN TRUE END;
    c := t; INC(i)
  END;
  r := c; RETURN FALSE
END Choose;

PROCEDURE Sqrt (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  x, bit, m: LONGCARD;
BEGIN
  m := n; x := 0; bit := 4611686018427387904;   (* 2^62 *)
  WHILE bit > m DO bit := bit DIV 4 END;
  WHILE bit # 0 DO
    IF m >= x + bit THEN m := m - (x + bit); x := x DIV 2 + bit ELSE x := x DIV 2 END;
    bit := bit DIV 4
  END;
  r := x; RETURN FALSE
END Sqrt;

PROCEDURE MinFac (n: LONGCARD; VAR r: LONGCARD) : BOOLEAN;
VAR
  d: LONGCARD;
BEGIN
  IF n = 0 THEN r := 2; RETURN FALSE END;
  IF n = 1 THEN r := 1; RETURN FALSE END;
  IF n MOD 2 = 0 THEN r := 2; RETURN FALSE END;
  d := 3;
  WHILE d <= n DIV d DO
    IF n MOD d = 0 THEN r := d; RETURN FALSE END;
    d := d + 2
  END;
  r := n; RETURN FALSE
END MinFac;

PROCEDURE IsPrime (n: LONGCARD) : LONGCARD;
VAR
  m: LONGCARD;
BEGIN
  IF n < 2 THEN RETURN 0 END;
  IF MinFac(n, m) THEN RETURN 0 END;
  IF m = n THEN RETURN 1 ELSE RETURN 0 END
END IsPrime;

PROCEDURE Dvd (a, b: LONGCARD) : LONGCARD;
BEGIN
  IF a = 0 THEN
    IF b = 0 THEN RETURN 1 ELSE RETURN 0 END
  END;
  IF b MOD a = 0 THEN RETURN 1 ELSE RETURN 0 END
END Dvd;

END LM2Nat.
