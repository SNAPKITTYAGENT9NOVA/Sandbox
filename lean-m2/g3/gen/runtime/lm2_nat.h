/* LEAN-M2-CC-001 MathIR v1 runtime: checked operations on 64-bit unsigned integers with
 * Lean ℕ semantics. Each returns 1 on overflow (result NOT written), 0 otherwise.
 *   sub truncates at 0 (ℕ subtraction)   div: x / 0 = 0   mod: x % 0 = x   pow: 0^0 = 1
 * Hand-written, fixed (not generated). Compiled only by CompCert. */
#ifndef LM2_NAT_H
#define LM2_NAT_H
#include <stdint.h>

static int lm2_add(uint64_t a, uint64_t b, uint64_t *r) {
  if (a > UINT64_MAX - b) return 1;
  *r = a + b; return 0;
}
static int lm2_mul(uint64_t a, uint64_t b, uint64_t *r) {
  if (a != 0u && b > UINT64_MAX / a) return 1;
  *r = a * b; return 0;
}
static int lm2_sub(uint64_t a, uint64_t b, uint64_t *r) {
  *r = (a > b) ? a - b : 0u; return 0;
}
static int lm2_div(uint64_t a, uint64_t b, uint64_t *r) {
  *r = (b == 0u) ? 0u : a / b; return 0;
}
static int lm2_mod(uint64_t a, uint64_t b, uint64_t *r) {
  *r = (b == 0u) ? a : a % b; return 0;
}
/* Square-and-multiply. For a >= 2, a^e >= 2^e, so e >= 64 always overflows. A squaring is
 * performed only while exponent bits remain, so an overflow there is a genuine overflow. */
static int lm2_pow(uint64_t a, uint64_t e, uint64_t *r) {
  uint64_t acc = 1u, base = a;
  if (e == 0u) { *r = 1u; return 0; }
  if (a == 0u) { *r = 0u; return 0; }
  if (a == 1u) { *r = 1u; return 0; }
  if (e >= 64u) return 1;
  for (;;) {
    if (e & 1u) { if (lm2_mul(acc, base, &acc)) return 1; }
    e >>= 1;
    if (e == 0u) break;
    if (lm2_mul(base, base, &base)) return 1;
  }
  *r = acc; return 0;
}

/* ---- MathIR v2 builtins (Lean / Mathlib semantics) ---- */
static uint64_t lm2_min(uint64_t a, uint64_t b) { return a < b ? a : b; }
static uint64_t lm2_max(uint64_t a, uint64_t b) { return a < b ? b : a; }
/* Nat.gcd: gcd 0 b = b, gcd a 0 = a, gcd 0 0 = 0 */
static int lm2_gcd(uint64_t a, uint64_t b, uint64_t *r) {
  while (b != 0u) { uint64_t t = a % b; a = b; b = t; }
  *r = a; return 0;
}
/* Nat.lcm a b = a * b / gcd a b; lcm 0 b = lcm a 0 = 0 */
static int lm2_lcm(uint64_t a, uint64_t b, uint64_t *r) {
  uint64_t g;
  if (a == 0u || b == 0u) { *r = 0u; return 0; }
  lm2_gcd(a, b, &g);
  return lm2_mul(a / g, b, r);
}
/* Nat.factorial: 0! = 1. 21! > 2^64. */
static int lm2_fact(uint64_t n, uint64_t *r) {
  uint64_t acc = 1u, i;
  if (n > 20u) return 1;
  for (i = 2u; i <= n; i++) acc *= i;
  *r = acc; return 0;
}
/* Nat.choose n k = 0 if k > n. Multiplicative formula over min(k, n-k); each partial product
 * C(n-k+i, i) is an exact integer; overflow of an intermediate is reported (sound, may be incomplete). */
static int lm2_choose(uint64_t n, uint64_t k, uint64_t *r) {
  uint64_t c = 1u, i, g, num, den, t;
  if (k > n) { *r = 0u; return 0; }
  if (k > n - k) k = n - k;
  for (i = 1u; i <= k; i++) {
    /* c := c * (n - k + i) / i, computed without losing exactness: divide by gcd first */
    num = n - k + i; den = i;
    lm2_gcd(c, den, &g); c /= g; den /= g;
    lm2_gcd(num, den, &g); num /= g; den /= g;   /* now den == 1 */
    if (lm2_mul(c, num, &t)) return 1;
    c = t;
  }
  *r = c; return 0;
}
/* Nat.sqrt: floor of the square root */
static int lm2_sqrt(uint64_t n, uint64_t *r) {
  uint64_t x = 0u, bit = (uint64_t)1u << 62;
  while (bit > n) bit >>= 2;
  while (bit != 0u) {
    if (n >= x + bit) { n -= x + bit; x = (x >> 1) + bit; } else { x >>= 1; }
    bit >>= 2;
  }
  *r = x; return 0;
}
/* Nat.minFac: minFac 0 = 2, minFac 1 = 1, otherwise the least prime factor (trial division) */
static int lm2_minfac(uint64_t n, uint64_t *r) {
  uint64_t d;
  if (n == 0u) { *r = 2u; return 0; }
  if (n == 1u) { *r = 1u; return 0; }
  if (n % 2u == 0u) { *r = 2u; return 0; }
  for (d = 3u; d <= n / d; d += 2u) { if (n % d == 0u) { *r = d; return 0; } }
  *r = n; return 0;
}
/* Nat.Prime n  <->  n >= 2 and minFac n = n */
static uint64_t lm2_isprime(uint64_t n) {
  uint64_t m;
  if (n < 2u) return 0u;
  lm2_minfac(n, &m);
  return m == n ? 1u : 0u;
}
/* a ∣ b on ℕ: 0 ∣ b iff b = 0 */
static uint64_t lm2_dvd(uint64_t a, uint64_t b) { return a == 0u ? (b == 0u) : (b % a == 0u); }
#endif
