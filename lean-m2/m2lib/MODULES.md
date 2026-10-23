# Module inventory

Each module has a `.def` interface and a `.mod` implementation in `src/`. "Tests" names the program in `tests/` that checks it.

## Implemented

| Module | Exports | What it provides | Capacity / bounds | Tests |
|---|---|---|---|---|
| NatArith | 25 | Lean `ℕ` on 64 bits: truncated `-`, `x/0 = 0`, `x%0 = x`, `0^0 = 1`, `Nat.sqrt`, `Nat.log`/`log2`/`clog`, bitwise operations | `Add`/`Mul`/`Pow`/`ShiftLeft` return FALSE above 2^64 − 1 | TestCore |
| NumberTheory | 32 | gcd/lcm, modular `+ × ^`, `minFac`, primes, π, Ω/ω, `padicValNat`, `factorization`, radical, squarefree/powerful/prime-power predicates, σ_k, φ, μ, Legendre and Jacobi symbols | Uses trial division, so the cost grows with √(largest prime factor) | TestCore |
| ModArith | 14 | Modular inverse, CRT (non-coprime moduli allowed), deterministic Miller–Rabin, Pollard–Brent factorisation, multiplicative order, Carmichael λ, primitive roots, Tonelli–Shanks, baby-step giant-step | Full 64-bit range; `DiscreteLog` only for m ≤ 2^40 | TestCore |
| BigNat | 22 | Exact naturals in base 2^32: Knuth D division, Newton square root, gcd/lcm, decimal I/O | 8192 bits; FALSE beyond that | TestBig |
| BigInt | 23 | Signed exact integers; `Int.ediv`/`emod` (Euclidean), `toNat`, `natAbs` | 8192-bit magnitude | TestBig |
| Rat | 25 | `ℚ` in lowest terms; `x/0 = 0`, `0⁻¹ = 0`; integer powers; `Int.floor`, `Int.ceil`, `Nat.floor` | Numerator and denominator up to 8192 bits each | TestBig |
| Combinatorics | 20 | Factorials, binomials, Fibonacci/Lucas, Catalan, partitions, derangements, Stirling numbers of the second kind, `bernoulli`/`bernoulli'`, `harmonic` | 64-bit and BigNat variants; partitions n ≤ 2048, Stirling n ≤ 512, Bernoulli n ≤ 256 | TestCore, TestBig |
| Digits | 13 | `Nat.digits` with Mathlib's edge cases for base 0 and base 1, `ofDigits`, digit sum/count/product, reversal, palindromes, decimal concatenation | Lists of up to 64 digits | TestCore |
| NatSeq | 42 | `List ℕ` and `Finset ℕ` operations: range/Icc/Ico/Ioc, filter, map, sum, prod, count, sort, dedup, union/inter/diff, `divisors`, `primeFactorsList`, `primesBelow` | 4096 elements | TestSeq |
| NatSearch | 26 | `Nat.count`, a bounded `Nat.nth`/`Nat.find`, and 20 predicates (prime, squarefree, powerful, perfect, abundant, pseudoperfect, weird, triangular, practical, Carmichael, …) | Searches stop at an explicit limit and return FALSE if no witness is found; pseudoperfect/practical n ≤ 2^20 | TestSearch |
| Matrix | 15 | Integer matrices (exact determinant via Bareiss in BigInt, products, powers, powers mod m) and rational matrices (determinant, rank, Lean-style inverse with a singular matrix giving 0) | n ≤ 16 | TestBig |
| Poly | 24 | `ℚ[X]`: ring operations, `eval`, `derivative`, `comp`, division with remainder (`p / 0 = 0`, `p % 0 = p`), monic gcd | Degree ≤ 48 | TestBig |
| OeisNat | 80 | ℕ-valued `def a` from 80 FormalConjectures/OEIS files, transcribed from the Lean source | 64-bit results; per-sequence bounds are stated in the `.def` | TestOeis |
| OeisInt | 29 | ℤ- and ℚ-valued (or ℚ-mediated) `def a` from 26 FormalConjectures/OEIS files (with the auxiliary `c`, `d` of A100434), plus `Int.xor` | Exact BigInt/Rat intermediates | TestOeis, TestSeq |

That is 390 exported procedures in total.

## Not implemented

- **Real-valued definitions** (`noncomputable def … : ℝ`, `Real.log`, limits, asymptotics) are not implemented. The library has no floating point and does not approximate.
- **Definitions over unbounded searches or sets** are not implemented: `Set ℕ`, `sInf`, and `Nat.find` without a bound. The bounded forms in NatSearch report FALSE instead of guessing.
- **ErdosProblems/*.lean definitions** have not been transcribed yet. Only FormalConjectures/OEIS was covered (105 files with term tests).
- **A007013 for n ≥ 4** returns FALSE because the result 2^127 − 1 does not fit the 64-bit output type.
- **A358684 for n = 7** returns FALSE: minFac (fermatNumber 7) is above the 2^32 trial-division bound.
- **The AArch64 target has not been tested.** Everything was built and run on x86_64 Linux. The code uses no target-specific features: it needs only a 64-bit `LONGCARD`/`LONGINT` and a 32-bit `CARDINAL`.
