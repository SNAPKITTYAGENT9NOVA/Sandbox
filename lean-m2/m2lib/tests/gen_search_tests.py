# Usage: python3 gen_search_tests.py > TestSearch.mod
# Expected values come from brute-force Python definitions of each predicate (divisor
# enumeration, subset sums, Fermat-test definition of Carmichael numbers), independent of the
# factorisation-based Modula-2 implementations.
from math import isqrt, gcd

def mf(n):
    if n < 2: return 1 if n == 1 else 2
    d = 2
    while d * d <= n:
        if n % d == 0: return d
        d += 1
    return n
def pr(n): return n >= 2 and mf(n) == n
def pfl(n):
    o = []
    while n > 1: p = mf(n); o.append(p); n //= p
    return o
def divs(n): return [d for d in range(1, n + 1) if n % d == 0] if n else []
def sqf(n): return n != 0 and len(pfl(n)) == len(set(pfl(n)))
def powf(n): return n == 0 or all(pfl(n).count(p) >= 2 for p in set(pfl(n)))
def ps(n): return sum(divs(n)) - n if n else 0
def perfect(n): return n > 0 and ps(n) == n
def abund(n): return n < ps(n)
def defic(n): return ps(n) < n
def subsetsum(ds, t):
    r = {0}
    for d in ds: r |= {x + d for x in r if x + d <= t}
    return r
def pseudo(n): return n > 0 and n in subsetsum(divs(n)[:-1], n)
def weird(n): return abund(n) and not pseudo(n)
def tri(n): k = (isqrt(8 * n + 1) - 1) // 2; return k * (k + 1) // 2 == n
def pal(n): s = str(n); return s == s[::-1]
def refac(n): return n > 0 and n % len(divs(n)) == 0
def twin(n): return pr(n) and pr(n + 2)
def sg(n): return pr(n) and pr(2 * n + 1)
def practical(n):
    if n == 0: return False
    r = subsetsum(divs(n), n); return all(m in r for m in range(1, n + 1))
def carm(n): return n > 2 and not pr(n) and all(pow(a, n - 1, n) == 1 for a in range(1, n) if gcd(a, n) == 1)

preds = {'Prime': pr, 'Composite': lambda n: n > 1 and not pr(n), 'Squarefree': sqf, 'Powerful': powf,
         'Square': lambda n: isqrt(n) ** 2 == n, 'PrimePow': lambda n: n > 1 and len(set(pfl(n))) == 1,
         'Even': lambda n: n % 2 == 0, 'Odd': lambda n: n % 2 == 1, 'Perfect': perfect, 'Abundant': abund,
         'Deficient': defic, 'Pseudoperfect': pseudo, 'Weird': weird, 'Triangular': tri, 'Palindrome10': pal,
         'Refactorable': refac, 'TwinPrime': twin, 'SophieGermain': sg, 'Practical': practical, 'Carmichael': carm}
L = []
N = 1200
for name, f in preds.items():
    vals = [n for n in range(N + 1) if f(n)]
    c = sum(1 for n in range(1000) if f(n))
    L.append(f'  Check.Nat("Count {name} < 1000", 1000, TRUE, NatSearch.Count(NatSearch.{name}, 1000), {c});')
    for k in [0, 1, 4]:
        if k < len(vals):
            L.append(f'  ok := NatSearch.Nth(NatSearch.{name}, {k}, {N}, r);')
            L.append(f'  Check.Nat("Nth {name}", {k}, ok, r, {vals[k]});')
    L.append(f'  ok := NatSearch.Nth(NatSearch.{name}, {len(vals)}, {N}, r);')
    L.append(f'  Check.Fails("Nth {name} beyond limit", {len(vals)}, ok);')
    g = [n for n in range(500) if f(n)]
    if g:
        L.append(f'  ok := NatSearch.GreatestBelow(NatSearch.{name}, 500, r);')
        L.append(f'  Check.Nat("GreatestBelow {name} 500", 500, ok, r, {g[-1]});')
    L.append(f'  Check.Nat("CountIcc {name} [100, 300]", 100, TRUE, NatSearch.CountIcc(NatSearch.{name}, 100, 300), {sum(1 for n in range(100, 301) if f(n))});')
    fr = [n for n in range(777, N + 1) if f(n)]
    L.append(f'  ok := NatSearch.FindFrom(NatSearch.{name}, 777, {N}, r);')
    L.append(f'  Check.Nat("FindFrom {name} 777", 777, ok, r, {fr[0]});' if fr else f'  Check.Fails("FindFrom {name} 777", 777, ok);')
L.append('  Check.True("Triangular 2^64-1 false", NOT NatSearch.Triangular(18446744073709551615));')
k = 6000000000
L.append(f'  Check.True("Triangular large", NatSearch.Triangular({k * (k + 1) // 2}) AND NOT NatSearch.Triangular({k * (k + 1) // 2 + 1}));')
L.append('  Check.True("Prime 2^64-59", NatSearch.Prime(18446744073709551557));')
L.append('  Check.True("TwinPrime at the top is false", NOT NatSearch.TwinPrime(18446744073709551557));')
L.append('  Check.True("Pseudoperfect beyond bound", NOT NatSearch.Pseudoperfect(2000000));')
L.append('  ok := NatSearch.Find(NatSearch.Perfect, 10, r); Check.Nat("Find Perfect", 10, ok, r, 6);')
L.append('  ok := NatSearch.Find(NatSearch.Perfect, 5, r); Check.Fails("Find Perfect <= 5", 5, ok);')
L.append('  ok := NatSearch.Nth(NatSearch.Perfect, 3, 9000, r); Check.Nat("4th perfect", 3, ok, r, 8128);')
L.append('  ok := NatSearch.Nth(NatSearch.Weird, 1, 1000, r); Check.Nat("2nd weird", 1, ok, r, 836);')
L.append('  ok := NatSearch.Nth(NatSearch.Carmichael, 5, 7000, r); Check.Nat("6th Carmichael", 5, ok, r, 6601);')
L.append(f'  Check.Nat("Count Prime < 10^5", 0, TRUE, NatSearch.Count(NatSearch.Prime, 100000), {sum(1 for n in range(100000) if pr(n))});')
print('''(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE TestSearch;
(* NatSearch: Nat.count / Nat.nth / Nat.find over the predicate catalogue, against brute-force
   Python definitions (tests/gen_search_tests.py). *)

IMPORT Check, NatSearch;

VAR
  r: LONGCARD; ok: BOOLEAN;

BEGIN''')
print("\n".join(L))
print('''  Check.Done("TestSearch")
END TestSearch.''')
