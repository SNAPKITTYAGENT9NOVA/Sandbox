# Usage: python3 gen_core_tests.py > TestCore.mod
# Expected values come from the naive Python definitions below (direct transcriptions of the
# Mathlib definitions: trial division, divisor enumeration, Fraction arithmetic), independent
# of the Modula-2 algorithms they check.
from fractions import Fraction
from math import comb, factorial, gcd, isqrt
from functools import lru_cache

M64 = 2**64

def minfac(n):
    if n == 0: return 2
    if n == 1: return 1
    d = 2
    while d * d <= n:
        if n % d == 0: return d
        d += 1
    return n
def isprime(n): return n >= 2 and minfac(n) == n
@lru_cache(None)
def pfl_t(n): return tuple(pfl_raw(n))
def pfl(n): return list(pfl_t(n))
def pfl_raw(n):
    out = []
    while n > 1:
        p = minfac(n); out.append(p); n //= p
    return out
@lru_cache(None)
def divisors(n): return tuple(d for d in range(1, n + 1) if n % d == 0) if n else ()
def padic(p, n):
    if p <= 1 or n == 0: return 0
    k = 0
    while n % p == 0: n //= p; k += 1
    return k
def radical(n):
    r = 1
    for p in set(pfl(n)): r *= p
    return r
def sqfpart(n):
    if n == 0: return 1
    r = 1
    for p in set(pfl(n)):
        if pfl(n).count(p) % 2: r *= p
    return r
def squarefree(n): return n != 0 and all(pfl(n).count(p) == 1 for p in set(pfl(n)))
def primepow(n): return n > 1 and len(set(pfl(n))) == 1
def powerful(n): return n == 0 or all(pfl(n).count(p) >= 2 for p in set(pfl(n)))
@lru_cache(None)
def totient(n): return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1) if n else 0
def moebius(n):
    if n == 0: return 0
    if not squarefree(n): return 0
    return (-1) ** len(pfl(n))
def legendre(a, p):
    if p == 2: return a % 2
    v = pow(a % p, (p - 1) // 2, p)
    return -1 if v == p - 1 else v
def jacobi(a, b):
    r = 1
    for p in pfl(b): r *= legendre(a, p)
    return r
def log(b, n):
    if b <= 1: return 0
    k = 0
    while b ** (k + 1) <= n: k += 1
    return k
def clog(b, n):
    if b <= 1 or n <= 1: return 0
    k = 0
    while b ** k < n: k += 1
    return k
def nth_prime(k):
    c = -1; p = 1
    while True:
        p += 1
        if isprime(p):
            c += 1
            if c == k: return p
def digits(b, n):
    if n == 0: return []
    if b == 0: return [n]
    if b == 1: return [1] * n
    out = []
    while n: out.append(n % b); n //= b
    return out
def ofdigits(b, l):
    return sum(d * b ** i for i, d in enumerate(l))
def bernoulli_plus(n):
    B = []
    for m in range(n + 1):
        B.append(1 - sum(Fraction(comb(m, k), m - k + 1) * B[k] for k in range(m)))
    return B[n]
def bernoulli(n): return (-1) ** n * bernoulli_plus(n)
def harmonic(n): return sum((Fraction(1, i + 1) for i in range(n)), Fraction(0))
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
def derange(n):
    d = [1, 0]
    for i in range(2, n + 1): d.append((i - 1) * (d[-1] + d[-2]))
    return d[n]
def fib(n):
    a, b = 0, 1
    for _ in range(n): a, b = b, a + b
    return a
def lucas(n):
    a, b = 2, 1
    for _ in range(n): a, b = b, a + b
    return a
def dfact(n):
    r = 1
    while n > 1: r *= n; n -= 2
    return r
def order(a, m):
    if m == 0: return 0
    if m == 1: return 1
    if gcd(a, m) != 1: return 0
    k = 1; x = a % m
    while x != 1: x = x * a % m; k += 1
    return k
def lam(n):
    if n == 0: return 0
    from math import lcm
    r = 1
    for a in range(1, n + 1):
        if gcd(a, n) == 1: r = lcm(r, order(a, n))
    return r
def primroot(m):
    if m == 1: return 0
    phi = totient(m)
    for g in range(1, m):
        if gcd(g, m) == 1 and order(g, m) == phi: return g
    return None
def sqrtmod(a, p):
    for r in range(p):
        if r * r % p == a % p: return r
    return None
def dlog(g, h, m):
    x = 1 % m
    for k in range(4 * m + 70):
        if x == h % m: return k
        x = x * g % m
    return None
def crt(a1, m1, a2, m2):
    from math import lcm
    L = lcm(m1, m2)
    for x in range(L):
        if x % m1 == a1 % m1 and x % m2 == a2 % m2: return x, L
    return None

out = []
def emit(s): out.append('  ' + s)
def nat(name, arg, call, v):
    emit(f'ok := {call};')
    if 0 <= v < M64: emit(f'Check.Nat("{name}", {arg}, ok, n, {v});')
    else: emit(f'Check.Fails("{name}", {arg}, ok);')
def natv(name, arg, expr, v):           # a procedure returning LONGCARD directly
    emit(f'Check.Nat("{name}", {arg}, TRUE, {expr}, {v});')
def intv(name, arg, expr, v):
    emit(f'Check.Int("{name}", {arg}, TRUE, {expr}, {v});')
def boolv(name, expr, v):
    emit(f'Check.True("{name}", ({expr}) = {"TRUE" if v else "FALSE"});')

# ---- NatArith
pairs = [(0, 0), (0, 5), (5, 0), (7, 3), (3, 7), (M64 - 1, 1), (M64 - 1, M64 - 1), (2**32, 2**32), (2**32 - 1, 2**32 + 1)]
for a, b in pairs:
    nat('NatArith.Add', a, f'NatArith.Add({a}, {b}, n)', a + b)
    nat('NatArith.Mul', a, f'NatArith.Mul({a}, {b}, n)', a * b)
    natv('NatArith.Sub', a, f'NatArith.Sub({a}, {b})', max(a - b, 0))
    natv('NatArith.Div', a, f'NatArith.Div({a}, {b})', a // b if b else 0)
    natv('NatArith.Mod', a, f'NatArith.Mod({a}, {b})', a % b if b else a)
    natv('NatArith.Dist', a, f'NatArith.Dist({a}, {b})', abs(a - b))
    natv('NatArith.Xor', a, f'NatArith.Xor({a}, {b})', a ^ b)
    natv('NatArith.LAnd', a, f'NatArith.LAnd({a}, {b})', a & b)
    natv('NatArith.LOr', a, f'NatArith.LOr({a}, {b})', a | b)
    boolv(f'NatArith.Dvd({a},{b})', f'NatArith.Dvd({a}, {b})', (b == 0) if a == 0 else b % a == 0)
for a, e in [(0, 0), (0, 3), (1, 10**18), (2, 63), (2, 64), (3, 40), (3, 41), (10, 19), (10, 20), (M64 - 1, 1)]:
    nat('NatArith.Pow', a, f'NatArith.Pow({a}, {e}, n)', a ** e)
for x in [0, 1, 2, 3, 4, 15, 16, 17, 99, 10**12, 10**12 + 1, M64 - 1, 2**62]:
    natv('NatArith.Sqrt', x, f'NatArith.Sqrt({x})', isqrt(x))
    boolv(f'NatArith.IsSquare({x})', f'NatArith.IsSquare({x})', isqrt(x) ** 2 == x)
    natv('NatArith.Log2', x, f'NatArith.Log2({x})', x.bit_length() - 1 if x else 0)
    natv('NatArith.PopCount', x, f'NatArith.PopCount({x})', bin(x).count('1'))
    natv('NatArith.Pred', x, f'NatArith.Pred({x})', max(x - 1, 0))
for b, x in [(0, 5), (1, 5), (2, 0), (2, 1), (2, 1023), (2, 1024), (10, 999), (10, 1000), (10, M64 - 1), (3, 2**63), (7, 1)]:
    natv('NatArith.Log', x, f'NatArith.Log({b}, {x})', log(b, x))
    natv('NatArith.Clog', x, f'NatArith.Clog({b}, {x})', clog(b, x))
for a, k in [(1, 0), (1, 63), (1, 64), (3, 62), (3, 63), (0, 100), (M64 - 1, 0)]:
    nat('NatArith.ShiftLeft', a, f'NatArith.ShiftLeft({a}, {k}, n)', a << k)
for a, k in [(M64 - 1, 0), (M64 - 1, 63), (M64 - 1, 64), (M64 - 1, 1000), (12345, 3)]:
    natv('NatArith.ShiftRight', a, f'NatArith.ShiftRight({a}, {k})', a >> k)
for x, i in [(5, 0), (5, 1), (5, 2), (2**63, 63), (2**63, 64), (M64 - 1, 1000)]:
    boolv(f'NatArith.TestBit({x},{i})', f'NatArith.TestBit({x}, {i})', (x >> i) & 1 == 1)

# ---- NumberTheory
for a, b in [(0, 0), (0, 9), (12, 18), (17, 31), (2**40, 2**20 * 3), (M64 - 1, M64 - 3)]:
    natv('NumberTheory.Gcd', a, f'NumberTheory.Gcd({a}, {b})', gcd(a, b))
    nat('NumberTheory.Lcm', a, f'NumberTheory.Lcm({a}, {b}, n)', a * b // gcd(a, b) if a and b else 0)
    boolv(f'NumberTheory.Coprime({a},{b})', f'NumberTheory.Coprime({a}, {b})', gcd(a, b) == 1)
for a, b, m in [(0, 0, 1), (5, 7, 3), (M64 - 1, M64 - 1, M64 - 59), (2**63, 2**63, 1000000007)]:
    natv('NumberTheory.MulMod', a, f'NumberTheory.MulMod({a}, {b}, {m})', a * b % m)
    natv('NumberTheory.AddMod', a, f'NumberTheory.AddMod({a}, {b}, {m})', (a + b) % m)
for a, e, m in [(2, 10, 1000), (3, 0, 7), (3, 0, 1), (0, 0, 5), (7, 10**18, 10**9 + 7), (5, 3, 0)]:
    natv('NumberTheory.PowMod', a, f'NumberTheory.PowMod({a}, {e}, {m})', pow(a, e, m) if m > 1 else 0)
ns = [0, 1, 2, 3, 4, 6, 12, 25, 36, 60, 97, 100, 128, 210, 360, 997, 1001, 1024, 9973, 65536, 720720, 999983, 1000000]
for n in ns:
    natv('NumberTheory.MinFac', n, f'NumberTheory.MinFac({n})', minfac(n))
    boolv(f'NumberTheory.IsPrime({n})', f'NumberTheory.IsPrime({n})', isprime(n))
    natv('NumberTheory.BigOmega', n, f'NumberTheory.BigOmega({n})', len(pfl(n)))
    natv('NumberTheory.Omega', n, f'NumberTheory.Omega({n})', len(set(pfl(n))))
    natv('NumberTheory.MaxPrimeFac', n, f'NumberTheory.MaxPrimeFac({n})', max(pfl(n)) if n > 1 else 0)
    natv('NumberTheory.Radical', n, f'NumberTheory.Radical({n})', radical(n))
    natv('NumberTheory.SquarefreePart', n, f'NumberTheory.SquarefreePart({n})', sqfpart(n))
    boolv(f'NumberTheory.IsSquarefree({n})', f'NumberTheory.IsSquarefree({n})', squarefree(n))
    boolv(f'NumberTheory.IsPrimePow({n})', f'NumberTheory.IsPrimePow({n})', primepow(n))
    boolv(f'NumberTheory.IsPowerful({n})', f'NumberTheory.IsPowerful({n})', powerful(n))
    natv('NumberTheory.DivisorCount', n, f'NumberTheory.DivisorCount({n})', len(divisors(n)))
    for k in [0, 1, 2, 3]:
        nat(f'NumberTheory.DivisorSigma{k}', n, f'NumberTheory.DivisorSigma({k}, {n}, n)', sum(d ** k for d in divisors(n)))
    nat('NumberTheory.ProperDivisorSum', n, f'NumberTheory.ProperDivisorSum({n}, n)', sum(divisors(n)) - n if n else 0)
    boolv(f'NumberTheory.IsPerfect({n})', f'NumberTheory.IsPerfect({n})', n > 0 and sum(divisors(n)) == 2 * n)
    natv('NumberTheory.Totient', n, f'NumberTheory.Totient({n})', totient(n))
    intv('NumberTheory.Moebius', n, f'VAL(LONGINT, NumberTheory.Moebius({n}))', moebius(n))
    natv('NumberTheory.UnitaryDivisorCount', n, f'NumberTheory.UnitaryDivisorCount({n})', 2 ** len(set(pfl(n))) if n else 0)
    for p in [2, 3, 5, 7, 4, 1, 0]:
        natv(f'NumberTheory.PadicValNat{p}', n, f'NumberTheory.PadicValNat({p}, {n})', padic(p, n))
        natv(f'NumberTheory.Factorization{p}', n, f'NumberTheory.Factorization({n}, {p})', pfl(n).count(p) if isprime(p) else 0)
    for k in [0, 1, 2, 5]:
        l = pfl(n)
        natv('NumberTheory.PrimeFactorNth', n, f'NumberTheory.PrimeFactorNth({n}, {k})', l[k] if k < len(l) else 0)
for n in [0, 1, 2, 3, 10, 100, 1000, 7919, 10000]:
    natv('NumberTheory.PrimeCounting', n, f'NumberTheory.PrimeCounting({n})', sum(1 for p in range(n + 1) if isprime(p)))
    natv('NumberTheory.PrimeCountingBelow', n, f'NumberTheory.PrimeCountingBelow({n})', sum(1 for p in range(n) if isprime(p)))
    q = n
    while not isprime(q): q += 1
    nat('NumberTheory.NextPrime', n, f'NumberTheory.NextPrime({n}, n)', q)
for k in [0, 1, 2, 9, 99, 999]:
    nat('NumberTheory.NthPrime', k, f'NumberTheory.NthPrime({k}, n)', nth_prime(k))
for a in [-7, -1, 0, 1, 2, 3, 5, 10, 11, 1000003]:
    for b in [0, 1, 2, 3, 5, 9, 15, 21, 45, 97, 100, 1001]:
        intv(f'NumberTheory.Jacobi{b}', abs(a), f'VAL(LONGINT, NumberTheory.Jacobi({a}, {b}))', jacobi(a, b))
    for p in [2, 3, 7, 97]:
        intv(f'NumberTheory.Legendre{p}', abs(a), f'VAL(LONGINT, NumberTheory.Legendre({a}, {p}))', legendre(a, p))

# ---- ModArith
for a, m in [(3, 7), (10, 17), (6, 9), (0, 1), (5, 1), (1, 2), (M64 - 2, M64 - 1), (2, 0)]:
    v = pow(a, -1, m) if m > 1 and gcd(a, m) == 1 else (0 if m == 1 else None)
    emit(f'ok := ModArith.Inverse({a}, {m}, n);')
    if v is None: emit(f'Check.Fails("ModArith.Inverse", {a}, ok);')
    else: emit(f'Check.Nat("ModArith.Inverse", {a}, ok, n, {v});')
for a, m in [(3, 7), (0, 5), (9, 4), (M64 - 1, 10)]:
    natv('ModArith.SubMod', a, f'ModArith.SubMod({a}, 5, {m})', (a - 5) % m)
    natv('ModArith.NegMod', a, f'ModArith.NegMod({a}, {m})', (-a) % m)
for a1, m1, a2, m2 in [(2, 3, 3, 5), (1, 4, 3, 6), (1, 4, 2, 6), (0, 1, 0, 1), (5, 12, 11, 18), (7, 1000003, 11, 999983)]:
    r = crt(a1, m1, a2, m2) if m1 * m2 < 10**7 else None
    if m1 * m2 >= 10**7:
        from math import lcm
        L = lcm(m1, m2); x = next(x for x in range(a1 % m1, L, m1) if x % m2 == a2 % m2); r = (x, L)
    emit(f'ok := ModArith.Crt({a1}, {m1}, {a2}, {m2}, n, k);')
    if r is None: emit(f'Check.Fails("ModArith.Crt", {a1}, ok);')
    else:
        emit(f'Check.Nat("ModArith.Crt.x", {a1}, ok, n, {r[0]});')
        emit(f'Check.Nat("ModArith.Crt.m", {a1}, ok, k, {r[1]});')
big_primes = [2, 3, 97, 1000000007, 998244353, 2**61 - 1, 18446744073709551557]
big_comps = [0, 1, 4, 561, 1105, 3215031751, 2**61 + 1, 18446744073709551615, 4294967297, 1000000007 * 998244353, 3825123056546413051]
for p in big_primes: boolv(f'ModArith.IsPrime({p})', f'ModArith.IsPrime({p})', True)
for c in big_comps: boolv(f'ModArith.IsPrime({c})', f'ModArith.IsPrime({c})', False)
for n, mf in [(0, 2), (1, 1), (4294967297, 641), (1000000007 * 998244353, 998244353), (18446744073709551615, 3), (2**61 - 1, 2**61 - 1), (600851475143, 71), (999999999989 * 1000003, 1000003)]:
    natv('ModArith.MinFacFast', n, f'ModArith.MinFacFast({n})', mf)
for a, m in [(2, 7), (3, 7), (2, 1), (4, 6), (10, 11), (2, 1000003), (7, 0), (5, 2)]:
    natv('ModArith.Order', a, f'ModArith.Order({a}, {m})', order(a, m))
for n in [0, 1, 2, 4, 8, 16, 15, 24, 561, 1000]:
    nat('ModArith.CarmichaelLambda', n, f'ModArith.CarmichaelLambda({n}, n)', lam(n))
for m in [1, 2, 4, 7, 9, 18, 8, 12, 23, 50, 1000]:
    g = primroot(m)
    emit(f'ok := ModArith.PrimitiveRoot({m}, n);')
    if g is None: emit(f'Check.Fails("ModArith.PrimitiveRoot", {m}, ok);')
    else: emit(f'Check.Nat("ModArith.PrimitiveRoot", {m}, ok, n, {g});')
for a, p in [(2, 7), (3, 7), (0, 13), (10, 13), (5, 2), (4, 17), (2, 113), (3, 113), (5, 1000003)]:
    s = sqrtmod(a, p)
    emit(f'ok := ModArith.SqrtModPrime({a}, {p}, n);')
    if s is None: emit(f'Check.Fails("ModArith.SqrtModPrime", {a}, ok);')
    else: emit(f'Check.Nat("ModArith.SqrtModPrime", {a}, ok, n, {min(s, (p - s) % p)});')
emit('ok := ModArith.SqrtModPrime(4, 15, n);')
emit('Check.Fails("ModArith.SqrtModPrime(non-prime)", 15, ok);')
for g, h, m in [(2, 1, 11), (2, 3, 11), (3, 13, 17), (2, 5, 7), (2, 0, 8), (2, 4, 12), (5, 1, 1), (10, 7, 1000003)]:
    d = dlog(g, h, m)
    emit(f'ok := ModArith.DiscreteLog({g}, {h}, {m}, n);')
    if d is None: emit(f'Check.Fails("ModArith.DiscreteLog", {h}, ok);')
    else: emit(f'Check.Nat("ModArith.DiscreteLog", {h}, ok, n, {d});')
emit('x := ModArith.ExtGcd(240, 46, s, t);')
emit('Check.Int("ModArith.ExtGcd.g", 240, TRUE, x, 2);')
emit('Check.True("ModArith.ExtGcd.bezout", 240 * s + 46 * t = 2);')
emit('x := ModArith.ExtGcd(-35, 15, s, t);')
emit('Check.Int("ModArith.ExtGcd.g", 35, TRUE, x, 5);')
emit('Check.True("ModArith.ExtGcd.bezout2", -35 * s + 15 * t = 5);')
emit('x := ModArith.ExtGcd(0, 0, s, t);')
emit('Check.Int("ModArith.ExtGcd.g0", 0, TRUE, x, 0);')

# ---- Digits
for b, n in [(10, 0), (10, 7), (10, 1234567890), (2, 255), (0, 5), (1, 4), (0, 0), (1, 0), (3, 2**63), (16, M64 - 1), (7, 342)]:
    d = digits(b, n)
    natv('Digits.Length', n, f'Digits.Length({b}, {n})', len(d))
    natv('Digits.Sum', n, f'Digits.Sum({b}, {n})', sum(d))
    for k in [0, 1, 5]:
        natv('Digits.At', n, f'Digits.At({b}, {n}, {k})', d[k] if k < len(d) else 0)
    for dd in [0, 1, 7]:
        natv('Digits.Count', n, f'Digits.Count({b}, {n}, {dd})', d.count(dd))
        boolv(f'Digits.ContainsDigit({b},{n},{dd})', f'Digits.ContainsDigit({b}, {n}, {dd})', dd in d)
    nat('Digits.Reverse', n, f'Digits.Reverse({b}, {n}, n)', ofdigits(b, d[::-1]))
    boolv(f'Digits.IsPalindrome({b},{n})', f'Digits.IsPalindrome({b}, {n})', d == d[::-1])
    p = 1
    for x in d: p *= x
    nat('Digits.Product', n, f'Digits.Product({b}, {n}, n)', p)
    boolv(f'Digits.AllDistinct({b},{n})', f'Digits.AllDistinct({b}, {n})', len(set(d)) == len(d))
    emit(f'ok := Digits.ToDigits({b}, {n}, dl) AND Digits.OfDigits({b}, dl, n);')
    emit(f'Check.Nat("Digits.OfDigits∘ToDigits", {n}, ok, n, {n});')
emit('ok := Digits.ToDigits(1, 65, dl);')
emit('Check.Fails("Digits.ToDigits(base 1, 65)", 65, ok);')
for a, b in [(12, 345), (0, 0), (5, 0), (0, 7), (123456789, 1234567890), (1844674407, 3709551616)]:
    nat('Digits.Concat', a, f'Digits.Concat({a}, {b}, n)', a * 10 ** len(digits(10, b)) + b)

# ---- Combinatorics (64-bit)
for n in [0, 1, 5, 20, 21]:
    nat('Combinatorics.Factorial', n, f'Combinatorics.Factorial({n}, n)', factorial(n))
for n in [0, 1, 2, 7, 33, 34]:
    nat('Combinatorics.DoubleFactorial', n, f'Combinatorics.DoubleFactorial({n}, n)', dfact(n))
for n, k in [(0, 0), (5, 0), (5, 2), (5, 6), (10, 10), (40, 3), (2**32, 2), (100, 50), (67, 33), (68, 34), (M64 - 1, 1), (M64 - 1, M64 - 1)]:
    nat('Combinatorics.Choose', n, f'Combinatorics.Choose({n}, {k}, n)', comb(n, k))
    if n < 10**6:
        nat('Combinatorics.DescFactorial', n, f'Combinatorics.DescFactorial({n}, {k}, n)', factorial(n) // factorial(n - k) if k <= n else 0)
        a = 1
        for i in range(k): a *= n + i
        nat('Combinatorics.AscFactorial', n, f'Combinatorics.AscFactorial({n}, {k}, n)', a)
        nat('Combinatorics.Multichoose', n, f'Combinatorics.Multichoose({n}, {k}, n)', comb(n + k - 1, k) if n + k > 0 else (1 if k == 0 else 0))
for n in [0, 1, 2, 10, 33, 34]:
    nat('Combinatorics.CentralBinom', n, f'Combinatorics.CentralBinom({n}, n)', comb(2 * n, n))
    nat('Combinatorics.Catalan', n, f'Combinatorics.Catalan({n}, n)', comb(2 * n, n) // (n + 1))
for n in [0, 1, 2, 10, 93, 94]:
    nat('Combinatorics.Fib', n, f'Combinatorics.Fib({n}, n)', fib(n))
    nat('Combinatorics.Lucas', n, f'Combinatorics.Lucas({n}, n)', lucas(n))
for n in [0, 1, 2, 3, 10, 20, 21]:
    nat('Combinatorics.Derangements', n, f'Combinatorics.Derangements({n}, n)', derange(n))

body = "\n".join(out)
print(f'''(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE TestCore;
(* Checks NatArith, NumberTheory, ModArith, Digits and the 64-bit Combinatorics procedures
   against naive reference definitions (tests/gen_core_tests.py). A value of 2^64 or more
   must make the procedure return FALSE. *)

IMPORT Check, NatArith, NumberTheory, ModArith, Digits, Combinatorics;

VAR
  n, k: LONGCARD; x, s, t: LONGINT; ok: BOOLEAN; dl: Digits.List;

BEGIN
{body}
  Check.Done("TestCore")
END TestCore.''')
