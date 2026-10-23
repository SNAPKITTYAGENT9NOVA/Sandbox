# Usage: python3 gen_big_tests.py > TestBig.mod
# Expected values come from Python's exact int / Fraction arithmetic and naive definitions,
# independent of the Modula-2 algorithms (Knuth D, Bareiss, Gaussian elimination) under test.
import random
from fractions import Fraction
from math import comb, factorial, gcd, isqrt, lcm

random.seed(20261023)
CAP = 2**8192
out = []
def emit(s): out.append('  ' + s)

def big_ok(v): return 0 <= v < CAP
def int_ok(v): return abs(v) < CAP

def nat_text(name, call, v):
    emit(f'ok := {call};')
    if big_ok(v): emit(f'NatIs("{name}", a3, ok, "{v}");')
    else: emit(f'Check.Fails("{name}", 0, ok);')
def load_nat(var, v): emit(f'ok := BigNat.FromDecimal("{v}", {var}); Check.True("load", ok);')
def load_int(var, v): emit(f'ok := BigInt.FromDecimal("{v}", {var}); Check.True("load", ok);')

def ediv(a, b):
    if b == 0: return 0, a
    m = a % abs(b)
    return (a - m) // b, m

# ---- BigNat
vals = [0, 1, 2**32 - 1, 2**32, 2**64 - 1, 2**64, 10**40 + 7, 3**500, 2**4000 + 12345]
vals += [random.getrandbits(random.choice([31, 63, 65, 200, 1000, 3000, 4000])) for _ in range(14)]
for i in range(0, len(vals) - 1):
    a, b = vals[i], vals[i + 1] if i % 3 else vals[(i * 7) % len(vals)]
    load_nat('a1', a); load_nat('a2', b)
    nat_text('BigNat.Add', 'BigNat.Add(a1, a2, a3)', a + b)
    emit('BigNat.Sub(a1, a2, a3); ok := TRUE;'); emit(f'NatIs("BigNat.Sub", a3, ok, "{max(a - b, 0)}");')
    nat_text('BigNat.Mul', 'BigNat.Mul(a1, a2, a3)', a * b)
    emit('BigNat.DivMod(a1, a2, a3, a4); ok := TRUE;')
    q, m = (a // b, a % b) if b else (0, a)
    emit(f'NatIs("BigNat.DivMod.q", a3, ok, "{q}");')
    emit(f'NatIs("BigNat.DivMod.m", a4, ok, "{m}");')
    emit('BigNat.Gcd(a1, a2, a3); ok := TRUE;'); emit(f'NatIs("BigNat.Gcd", a3, ok, "{gcd(a, b)}");')
    nat_text('BigNat.Lcm', 'BigNat.Lcm(a1, a2, a3)', lcm(a, b))
    emit('BigNat.Sqrt(a1, a3); ok := TRUE;'); emit(f'NatIs("BigNat.Sqrt", a3, ok, "{isqrt(a)}");')
    emit(f'Check.Int("BigNat.Cmp", {i}, TRUE, VAL(LONGINT, BigNat.Cmp(a1, a2)), {(a > b) - (a < b)});')
    emit(f'Check.Nat("BigNat.BitLength", {i}, TRUE, VAL(LONGCARD, BigNat.BitLength(a1)), {a.bit_length()});')
    emit(f'ok := BigNat.ToNat(a1, n);')
    if a < 2**64: emit(f'Check.Nat("BigNat.ToNat", {i}, ok, n, {a});')
    else: emit(f'Check.Fails("BigNat.ToNat", {i}, ok);')
    emit(f'BigNat.DivModSmall(a1, 1000000007, a3, c); ok := TRUE;')
    emit(f'NatIs("BigNat.DivModSmall.q", a3, ok, "{a // 1000000007}");')
    emit(f'Check.Nat("BigNat.DivModSmall.r", {i}, TRUE, VAL(LONGCARD, c), {a % 1000000007});')
for base, e in [(0, 0), (2, 8191), (2, 8192), (3, 5000), (3, 5169), (10**100, 24), (10**100, 25), (1, 10**18)]:
    load_nat('a1', base)
    nat_text('BigNat.Pow', f'BigNat.Pow(a1, {e}, a3)', base ** e if e < 10**6 else 1)
emit('ok := BigNat.FromDecimal("12a", a1); Check.Fails("BigNat.FromDecimal(12a)", 0, ok);')
emit('ok := BigNat.FromDecimal("", a1); Check.Fails("BigNat.FromDecimal(empty)", 0, ok);')
emit(f'ok := BigNat.FromDecimal("{2**8192}", a1); Check.Fails("BigNat.FromDecimal(2^8192)", 0, ok);')

# ---- BigInt (Euclidean division as Int.ediv / Int.emod)
ivals = [0, 1, -1, 7, -7, 2**63, -2**63, -(2**63) - 1, 10**30 + 1, -(3**200)]
ivals += [random.choice([1, -1]) * random.getrandbits(random.choice([10, 64, 300, 2000])) for _ in range(10)]
for i in range(len(ivals)):
    a = ivals[i]; b = ivals[(i * 3 + 1) % len(ivals)]
    load_int('b1', a); load_int('b2', b)
    for nm, v in [('Add', a + b), ('Sub', a - b), ('Mul', a * b)]:
        emit(f'ok := BigInt.{nm}(b1, b2, b3);'); emit(f'IntIs("BigInt.{nm}", b3, ok, "{v}");')
    q, m = ediv(a, b)
    emit('ok := BigInt.DivMod(b1, b2, b3, b4);')
    emit(f'IntIs("BigInt.DivMod.q", b3, ok, "{q}");')
    emit(f'IntIs("BigInt.DivMod.m", b4, ok, "{m}");')
    emit(f'BigInt.Gcd(b1, b2, a3); ok := TRUE; NatIs("BigInt.Gcd", a3, ok, "{gcd(a, b)}");')
    emit(f'BigInt.ToNat(b1, a3); ok := TRUE; NatIs("BigInt.ToNat", a3, ok, "{max(a, 0)}");')
    emit(f'BigInt.NatAbs(b1, a3); ok := TRUE; NatIs("BigInt.NatAbs", a3, ok, "{abs(a)}");')
    emit(f'Check.Int("BigInt.Sign", {i}, TRUE, VAL(LONGINT, BigInt.Sign(b1)), {(a > 0) - (a < 0)});')
    emit('ok := BigInt.ToInt(b1, x);')
    if -2**63 <= a < 2**63: emit(f'Check.Int("BigInt.ToInt", {i}, ok, x, {a});')
    else: emit(f'Check.Fails("BigInt.ToInt", {i}, ok);')
for a, e in [(-2, 63), (-2, 64), (-3, 1001), (0, 0), (-1, 10**12)]:
    load_int('b1', a)
    emit(f'ok := BigInt.Pow(b1, {e}, b3);'); emit(f'IntIs("BigInt.Pow", b3, ok, "{a ** e if e < 10**6 else (-1) ** (e % 2)}");')

# ---- Rat
rvals = [Fraction(0), Fraction(1), Fraction(-1, 2), Fraction(22, 7), Fraction(-355, 113), Fraction(10**20, 3),
         Fraction(-(2**70) - 1, 2**65 + 3), Fraction(7, 10**25)]
def rtext(q): return str(q.numerator) if q.denominator == 1 else f'{q.numerator}/{q.denominator}'
for i in range(len(rvals)):
    a = rvals[i]; b = rvals[(i * 5 + 3) % len(rvals)]
    for var, q, nn, dd in [('r1', a, 'q1n', 'q1d'), ('r2', b, 'q2n', 'q2d')]:
        emit(f'ok := BigInt.FromDecimal("{q.numerator}", {nn}) AND BigNat.FromDecimal("{q.denominator}", {dd}) AND Rat.Make({nn}, {dd}, {var});')
        emit('Check.True("load rat", ok);')
    for nm, v in [('Add', a + b), ('Sub', a - b), ('Mul', a * b), ('Div', a / b if b else Fraction(0))]:
        emit(f'ok := Rat.{nm}(r1, r2, r3);'); emit(f'RatIs("Rat.{nm}", r3, ok, "{rtext(v)}");')
    emit(f'Rat.Inv(r1, r3); ok := TRUE; RatIs("Rat.Inv", r3, ok, "{rtext(1 / a if a else Fraction(0))}");')
    emit(f'Rat.Neg(r1, r3); ok := TRUE; RatIs("Rat.Neg", r3, ok, "{rtext(-a)}");')
    import math
    emit(f'ok := Rat.Floor(r1, b3); IntIs("Rat.Floor", b3, ok, "{math.floor(a)}");')
    emit(f'ok := Rat.Ceil(r1, b3); IntIs("Rat.Ceil", b3, ok, "{math.ceil(a)}");')
    emit(f'Rat.NatFloor(r1, a3); ok := TRUE; NatIs("Rat.NatFloor", a3, ok, "{max(math.floor(a), 0)}");')
    emit(f'ok := Rat.Cmp(r1, r2, ci); Check.Int("Rat.Cmp", {i}, ok, VAL(LONGINT, ci), {(a > b) - (a < b)});')
    for e in [0, 3, -2]:
        v = (a ** e) if (a != 0 or e >= 0) else Fraction(0)
        if a == 0 and e == 0: v = Fraction(1)
        emit(f'ok := Rat.ZPow(r1, {e}, r3); RatIs("Rat.ZPow{e}", r3, ok, "{rtext(v)}");')
emit('ok := Rat.MakeSmall(6, 0, r1); RatIs("Rat.MakeSmall(6/0)", r1, ok, "0");')
emit('ok := Rat.MakeSmall(-6, 4, r1); RatIs("Rat.MakeSmall(-6/4)", r1, ok, "-3/2");')

# ---- Combinatorics with BigNat / Rat results
def bern_plus(n):
    B = []
    for m in range(n + 1): B.append(1 - sum(Fraction(comb(m, k), m - k + 1) * B[k] for k in range(m)))
    return B[n]
def partitions(n):
    p = [1] + [0] * n
    for k in range(1, n + 1):
        for m in range(k, n + 1): p[m] += p[m - k]
    return p[n]
def stirling2(n, k):
    S = [[0] * (k + 1) for _ in range(n + 1)]; S[0][0] = 1
    for i in range(1, n + 1):
        for j in range(1, min(i, k) + 1): S[i][j] = j * S[i - 1][j] + S[i - 1][j - 1]
    return S[n][k]
def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a
for n in [0, 1, 25, 100, 900, 1000]:
    nat_text('Combinatorics.FactorialBig', f'Combinatorics.FactorialBig({n}, a3)', factorial(n))
for n, k in [(0, 0), (1000, 500), (8000, 4000), (9000, 4500), (10**6, 3), (5, 7)]:
    nat_text('Combinatorics.ChooseBig', f'Combinatorics.ChooseBig({n}, {k}, a3)', comb(n, k))
for n in [0, 1, 94, 1000, 11000, 12000]:
    nat_text('Combinatorics.FibBig', f'Combinatorics.FibBig({n}, a3)', fib(n))
for n in [0, 1, 34, 35, 200]:
    nat_text('Combinatorics.CatalanBig', f'Combinatorics.CatalanBig({n}, a3)', comb(2 * n, n) // (n + 1))
for n in [0, 1, 5, 100, 1000, 2048]:
    nat_text('Combinatorics.Partitions', f'Combinatorics.Partitions({n}, a3)', partitions(n))
emit('ok := Combinatorics.Partitions(2049, a3); Check.Fails("Combinatorics.Partitions(2049)", 2049, ok);')
for n, k in [(0, 0), (5, 0), (0, 5), (5, 2), (10, 10), (100, 50), (512, 3)]:
    nat_text('Combinatorics.StirlingSecond', f'Combinatorics.StirlingSecond({n}, {k}, a3)', stirling2(n, k))
emit('ok := Combinatorics.StirlingSecond(513, 3, a3); Check.Fails("Combinatorics.StirlingSecond(513)", 513, ok);')
for n in [0, 1, 2, 3, 4, 12, 20, 60, 100, 256]:
    bp = bern_plus(n)
    emit(f'ok := Combinatorics.BernoulliPlus({n}, r3); RatIs("Combinatorics.BernoulliPlus", r3, ok, "{rtext(bp)}");')
    emit(f'ok := Combinatorics.Bernoulli({n}, r3); RatIs("Combinatorics.Bernoulli", r3, ok, "{rtext((-1) ** n * bp)}");')
emit('ok := Combinatorics.Bernoulli(257, r3); Check.Fails("Combinatorics.Bernoulli(257)", 257, ok);')
for n in [0, 1, 2, 10, 100, 500]:
    h = sum((Fraction(1, i + 1) for i in range(n)), Fraction(0))
    emit(f'ok := Combinatorics.Harmonic({n}, r3); RatIs("Combinatorics.Harmonic", r3, ok, "{rtext(h)}");')

# ---- Matrix
def det(M):
    n = len(M)
    if n == 0: return Fraction(1)
    A = [[Fraction(x) for x in r] for r in M]; d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None: return Fraction(0)
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            for j in range(c, n): A[r][j] -= f * A[c][j]
    return d
def rank(M):
    n = len(M); A = [[Fraction(x) for x in r] for r in M]; rk = 0
    for c in range(n):
        p = next((r for r in range(rk, n) if A[r][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for r in range(rk + 1, n):
            f = A[r][c] / A[rk][c]
            for j in range(n): A[r][j] -= f * A[rk][j]
        rk += 1
    return rk
def set_int(M):
    emit(f'Matrix.IntZero({len(M)}, im);')
    for i, r in enumerate(M):
        for j, v in enumerate(r):
            if v: emit(f'im.a[{i}, {j}] := {v};')
mats = [[], [[5]], [[0, 1], [1, 0]], [[2, 0, 0], [0, 3, 0], [0, 0, 4]], [[1, 2], [2, 4]],
        [[0, 2, 1], [3, 0, 4], [5, 6, 0]],
        [[random.randint(-10**9, 10**9) for _ in range(8)] for _ in range(8)],
        [[random.randint(-10**18, 10**18) for _ in range(16)] for _ in range(16)],
        [[1 if (i * j) % 3 == 1 else 0 for j in range(10)] for i in range(10)],
        [[comb(i + j, i) for j in range(12)] for i in range(12)]]
for idx, M in enumerate(mats):
    set_int(M)
    d = det(M)
    emit(f'ok := Matrix.IntDet(im, b3); IntIs("Matrix.IntDet", b3, ok, "{int(d)}");')
    emit('Matrix.RatFromInt(im, rm);')
    emit(f'ok := Matrix.RatDet(rm, r3); RatIs("Matrix.RatDet", r3, ok, "{int(d)}");')
    emit(f'ok := Matrix.RatRank(rm, ci2); Check.Nat("Matrix.RatRank", {idx}, ok, VAL(LONGCARD, ci2), {rank(M)});')
# inverse of the 3x3 example, entry (0,0) and (2,1); singular inverse is zero
set_int([[0, 2, 1], [3, 0, 4], [5, 6, 0]])
def inverse(M):
    n = len(M); A = [[Fraction(x) for x in r] + [Fraction(int(i == j)) for j in range(n)] for i, r in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[p] = A[p], A[c]
        f = A[c][c]; A[c] = [x / f for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                g = A[r][c]; A[r] = [x - g * y for x, y in zip(A[r], A[c])]
    return [r[n:] for r in A]
INV = inverse([[0, 2, 1], [3, 0, 4], [5, 6, 0]])
emit('Matrix.RatFromInt(im, rm); ok := Matrix.RatInverse(rm, rm2);')
for i in range(3):
    for j in range(3):
        emit(f'RatIs("Matrix.RatInverse[{i},{j}]", rm2.a[{i}, {j}], ok, "{rtext(INV[i][j])}");')
emit('ok := Matrix.RatMul(rm, rm2, rm3); RatIs("Matrix.A*A⁻¹[1,1]", rm3.a[1, 1], ok, "1"); RatIs("Matrix.A*A⁻¹[1,2]", rm3.a[1, 2], ok, "0");')
set_int([[1, 2], [2, 4]])
emit('Matrix.RatFromInt(im, rm); ok := Matrix.RatInverse(rm, rm2); RatIs("Matrix.RatInverse(singular)", rm2.a[0, 0], ok, "0");')
# Fibonacci matrix powers
set_int([[1, 1], [1, 0]])
for e in [0, 1, 10, 91, 92]:
    emit(f'ok := Matrix.IntPow(im, {e}, im2);')
    v = fib(e)
    if v < 2**63 and fib(e + 1) < 2**63: emit(f'Check.Int("Matrix.IntPow(fib)", {e}, ok, im2.a[0, 1], {v});')
    else: emit(f'Check.Fails("Matrix.IntPow(fib)", {e}, ok);')
for e, m in [(10**18, 10**9 + 7), (0, 5), (5, 1)]:
    a, b = 0, 1
    v = None
    # fib(e) mod m by fast doubling
    def fd(k):
        if k == 0: return (0, 1)
        x, y = fd(k // 2); c = x * (2 * y - x) % m; d2 = (x * x + y * y) % m
        return (d2, (c + d2) % m) if k % 2 else (c, d2)
    v = fd(e)[0] % m
    emit(f'ok := Matrix.IntPowMod(im, {e}, {m}, im2); Check.Int("Matrix.IntPowMod(fib)", {e}, ok, im2.a[0, 1], {v});')
emit('ok := Matrix.IntPowMod(im, 3, 0, im2); Check.Fails("Matrix.IntPowMod(m=0)", 0, ok);')
emit('ok := Matrix.IntTrace(im, x); Check.Int("Matrix.IntTrace", 0, ok, x, 1);')
emit('Matrix.IntTranspose(im, im2); Check.True("Matrix.IntTranspose(symmetric)", Matrix.IntEqual(im, im2));')
set_int([[2**62, 0], [0, 1]])
emit('ok := Matrix.IntMul(im, im, im2); Check.Fails("Matrix.IntMul(overflow)", 0, ok);')

# ---- Poly (ℚ[X]); coefficient lists low → high, trailing zeros stripped
def pnorm(a):
    a = list(a)
    while a and a[-1] == 0: a.pop()
    return a
def padd(a, b):
    n = max(len(a), len(b)); return pnorm([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def pmul(a, b):
    if not a or not b: return []
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] += x * y
    return pnorm(r)
def pdivmod(a, b):
    if not b: return [], pnorm(a)
    a = [Fraction(x) for x in a]; q = [Fraction(0)] * max(len(a) - len(b) + 1, 1)
    while len(pnorm(a)) >= len(b):
        a = pnorm(a); sh = len(a) - len(b); f = a[-1] / b[-1]; q[sh] = f
        for i, y in enumerate(b): a[i + sh] -= f * y
        a = pnorm(a)
    return pnorm(q), pnorm(a)
def pgcd(a, b):
    a, b = pnorm(a), pnorm(b)
    while b: a, b = b, pdivmod(a, b)[1]
    return [x / a[-1] for x in a] if a else []
def peval(a, x): return sum((c * x ** i for i, c in enumerate(a)), Fraction(0))
def pderiv(a): return pnorm([i * a[i] for i in range(1, len(a))])
def pcomp(p, q):
    r = []
    for c in reversed(p): r = padd(pmul(r, q), [Fraction(c)])
    return r
def ptext(a): return '[' + ', '.join(rtext(Fraction(x)) for x in a) + ']'
def set_poly(var, a):
    emit(f'Poly.Zero({var});')
    for i, c in enumerate(a):
        c = Fraction(c)
        if c: emit(f'ok := Rat.MakeSmall({c.numerator}, {c.denominator}, r1) AND Poly.SetCoeff({var}, {i}, r1); Check.True("set coeff", ok);')
def poly_is(name, var, a): emit(f'PolyIs("{name}", {var}, ok, "{ptext(a)}");')
def apery(n): return [Fraction(comb(n, k) ** 2 * comb(n + k, k)) for k in range(n + 1)]
def polyP(n): return [Fraction(comb(2 * k, k) ** 2) for k in range(n + 1)]
def polyQ(n): return [Fraction(comb(2 * k, k) ** 2, k + 1) for k in range(n + 1)]
cases = [([], [1]), ([-1, 0, 1], [1, -2, 1]), ([1, 2, 3], [Fraction(1, 2), 0, 0, 7]),
         (apery(4), polyP(3)), (polyQ(5), [0, 1]), ([2, Fraction(-3, 4), 0, 5], [])]
for i, (a, b) in enumerate(cases):
    a = pnorm([Fraction(x) for x in a]); b = pnorm([Fraction(x) for x in b])
    set_poly('p1', a); set_poly('p2', b)
    emit('ok := Poly.Add(p1, p2, p3);'); poly_is('Poly.Add', 'p3', padd(a, b))
    emit('ok := Poly.Sub(p1, p2, p3);'); poly_is('Poly.Sub', 'p3', padd(a, [-x for x in b]))
    emit('ok := Poly.Mul(p1, p2, p3);'); poly_is('Poly.Mul', 'p3', pmul(a, b))
    q, m = pdivmod(a, b)
    emit('ok := Poly.DivMod(p1, p2, p3, p4);'); poly_is('Poly.DivMod.q', 'p3', q); poly_is('Poly.DivMod.m', 'p4', m)
    emit('ok := Poly.Gcd(p1, p2, p3);'); poly_is('Poly.Gcd', 'p3', pgcd(a, b))
    emit('ok := Poly.Derivative(p1, p3);'); poly_is('Poly.Derivative', 'p3', pderiv(a))
    emit('ok := Poly.Comp(p1, p2, p3);'); poly_is('Poly.Comp', 'p3', pcomp(a, b))
    emit(f'Check.Nat("Poly.NatDegree", {i}, TRUE, VAL(LONGCARD, Poly.NatDegree(p1)), {max(len(a) - 1, 0)});')
    for x in [Fraction(0), Fraction(1), Fraction(-3, 2)]:
        emit(f'ok := Rat.MakeSmall({x.numerator}, {x.denominator}, r1) AND Poly.Eval(p1, r1, r2);')
        emit(f'RatIs("Poly.Eval", r2, ok, "{rtext(peval(a, x))}");')
set_poly('p1', [-1, 1])
emit('ok := Poly.Pow(p1, 48, p3);'); poly_is('Poly.Pow 48', 'p3', pnorm([Fraction(comb(48, k) * (-1) ** (48 - k)) for k in range(49)]))
emit('ok := Poly.Pow(p1, 49, p3); Check.Fails("Poly.Pow degree 49 > MaxDeg", 49, ok);')
emit('ok := Rat.MakeSmall(1, 1, r1); Check.True("Poly.IsRoot", Poly.IsRoot(p1, r1));')
emit('Check.True("Poly.IsMonic", Poly.IsMonic(p1));')
# aperyPoly n evaluated at 1 is the Apéry number a n (5258.lean)
for n in [0, 1, 2, 3, 4, 10]:
    set_poly('p1', apery(n))
    emit('ok := Rat.MakeSmall(1, 1, r1) AND Poly.Eval(p1, r1, r2);')
    emit(f'RatIs("aperyPoly {n} at 1", r2, ok, "{sum(apery(n))}");')

body = "\n".join(out)
print(f'''(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE TestBig;
(* Checks BigNat, BigInt, Rat, the BigNat/Rat procedures of Combinatorics, and Matrix against
   Python's exact integer and Fraction arithmetic (tests/gen_big_tests.py). Values at or above
   BigNat's capacity (2^8192) must make the procedure return FALSE. *)

IMPORT Check, BigNat, BigInt, Rat, Combinatorics, Matrix, Poly;

VAR
  a1, a2, a3, a4: BigNat.T; b1, b2, b3, b4: BigInt.T; r1, r2, r3: Rat.T;
  q1n, q2n: BigInt.T; q1d, q2d: BigNat.T;
  im, im2: Matrix.IntMat; rm, rm2, rm3: Matrix.RatMat;
  n: LONGCARD; x: LONGINT; c: CARDINAL; ci: INTEGER; ci2: CARDINAL; ok: BOOLEAN;
  buf: ARRAY [0..5200] OF CHAR;
  p1, p2, p3, p4: Poly.T;

PROCEDURE NatIs (name: ARRAY OF CHAR; VAR v: BigNat.T; ok: BOOLEAN; want: ARRAY OF CHAR);
BEGIN
  IF ok THEN ok := BigNat.ToDecimal(v, buf) END;
  Check.Text(name, ok, buf, want)
END NatIs;

PROCEDURE IntIs (name: ARRAY OF CHAR; VAR v: BigInt.T; ok: BOOLEAN; want: ARRAY OF CHAR);
BEGIN
  IF ok THEN ok := BigInt.ToDecimal(v, buf) END;
  Check.Text(name, ok, buf, want)
END IntIs;

PROCEDURE PolyIs (name: ARRAY OF CHAR; VAR v: Poly.T; ok: BOOLEAN; want: ARRAY OF CHAR);
BEGIN
  IF ok THEN ok := Poly.ToText(v, buf) END;
  Check.Text(name, ok, buf, want)
END PolyIs;

PROCEDURE RatIs (name: ARRAY OF CHAR; VAR v: Rat.T; ok: BOOLEAN; want: ARRAY OF CHAR);
BEGIN
  IF ok THEN ok := Rat.ToText(v, buf) END;
  Check.Text(name, ok, buf, want)
END RatIs;

BEGIN
{body}
  Check.Done("TestBig")
END TestBig.''')
