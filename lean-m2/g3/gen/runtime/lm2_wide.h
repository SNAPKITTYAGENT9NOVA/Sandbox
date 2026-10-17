/* LEAN-M2-CC-001 MathIR wide runtime: exact fixed-capacity multi-precision ℕ and ℤ.
 *
 * Used only as the FALLBACK of a generated function: when its fast 64-bit evaluation reports
 * overflow, the same IR is re-evaluated here with exact intermediates, and the result is
 * returned iff it fits in 64 bits. Capacity is LM2W_LIMBS * 32 = 4224 bits, above the 2^4096
 * size budget of the reference interpreter, so every intermediate the reference admits fits.
 *
 * Every operation returns 0 on success and 1 on failure (capacity exceeded, or an argument
 * outside a builtin's supported range); a failure makes the generated function report
 * LM2_OVERFLOW, which is sound. Results are written through the last pointer, which may alias
 * an input (each operation computes into a local and copies). Semantics are Lean's ℕ / ℤ:
 * truncated subtraction, x / 0 = 0, x % 0 = x, 0^0 = 1, and the builtins of lm2_nat.h.
 * Hand-written, fixed (not generated). Compiled only by CompCert. */
#ifndef LM2_WIDE_H
#define LM2_WIDE_H
#include <stdint.h>
#include "lm2_nat.h"

#define LM2W_LIMBS 132

typedef struct { uint32_t n; uint32_t d[LM2W_LIMBS]; } lm2w;   /* n used limbs, d[n-1] != 0; 0 has n = 0 */
typedef struct { int neg; lm2w m; } lm2wi;                       /* sign-magnitude; 0 is never negative */

static void lm2w_norm(lm2w *a) { while (a->n > 0u && a->d[a->n - 1u] == 0u) a->n--; }
static void lm2w_set(lm2w *r, uint64_t x) {
  r->d[0] = (uint32_t)x; r->d[1] = (uint32_t)(x >> 32); r->n = 2u; lm2w_norm(r);
}
static int lm2w_get(const lm2w *a, uint64_t *x) {
  if (a->n > 2u) return 1;
  *x = (a->n > 0u ? (uint64_t)a->d[0] : 0u) | (a->n > 1u ? (uint64_t)a->d[1] << 32 : 0u);
  return 0;
}
static int lm2w_iszero(const lm2w *a) { return a->n == 0u; }
static int lm2w_cmp(const lm2w *a, const lm2w *b) {
  uint32_t i;
  if (a->n != b->n) return a->n < b->n ? -1 : 1;
  for (i = a->n; i > 0u; i--) {
    if (a->d[i - 1u] != b->d[i - 1u]) return a->d[i - 1u] < b->d[i - 1u] ? -1 : 1;
  }
  return 0;
}
static uint32_t lm2w_bitlen(const lm2w *a) {
  uint32_t top, k = 0u;
  if (a->n == 0u) return 0u;
  top = a->d[a->n - 1u];
  while (top != 0u) { top >>= 1; k++; }
  return (a->n - 1u) * 32u + k;
}
static int lm2w_add(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w t; uint32_t i, m = a->n > b->n ? a->n : b->n; uint64_t c = 0u;
  for (i = 0u; i < m; i++) {
    c += (uint64_t)(i < a->n ? a->d[i] : 0u) + (uint64_t)(i < b->n ? b->d[i] : 0u);
    t.d[i] = (uint32_t)c; c >>= 32;
  }
  if (c != 0u) { if (m == LM2W_LIMBS) return 1; t.d[m++] = (uint32_t)c; }
  t.n = m; *r = t; return 0;
}
/* truncated: a - b = 0 when a <= b */
static int lm2w_sub(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w t; uint32_t i; int64_t c = 0;
  if (lm2w_cmp(a, b) <= 0) { r->n = 0u; return 0; }
  for (i = 0u; i < a->n; i++) {
    c += (int64_t)a->d[i] - (int64_t)(i < b->n ? b->d[i] : 0u);
    t.d[i] = (uint32_t)((uint64_t)c & 0xFFFFFFFFu);
    c = (c < 0) ? -1 : 0;
  }
  t.n = a->n; lm2w_norm(&t); *r = t; return 0;
}
static int lm2w_mul(const lm2w *a, const lm2w *b, lm2w *r) {
  uint32_t buf[LM2W_LIMBS + 1u], i, j, m;
  if (a->n == 0u || b->n == 0u) { r->n = 0u; return 0; }
  m = a->n + b->n;                      /* the product has m - 1 or m limbs */
  if (m - 1u > LM2W_LIMBS) return 1;
  for (i = 0u; i < m; i++) buf[i] = 0u;
  for (i = 0u; i < a->n; i++) {
    uint64_t c = 0u;
    for (j = 0u; j < b->n; j++) {
      uint64_t p = (uint64_t)a->d[i] * b->d[j] + buf[i + j] + c;
      buf[i + j] = (uint32_t)p; c = p >> 32;
    }
    buf[i + b->n] = (uint32_t)c;
  }
  while (m > 0u && buf[m - 1u] == 0u) m--;
  if (m > LM2W_LIMBS) return 1;
  for (i = 0u; i < m; i++) r->d[i] = buf[i];
  r->n = m; return 0;
}
/* floor(t / 2^32) for signed t, without relying on implementation-defined >> of negatives */
static int64_t lm2w_fdiv32(int64_t t) { return t >= 0 ? t / 4294967296LL : -((-(t + 1)) / 4294967296LL) - 1; }
/* q = a / b, rem = a % b, b != 0 (Knuth, TAOCP vol. 2, 4.3.1, Algorithm D, 32-bit digits) */
static void lm2w_divmod(const lm2w *a, const lm2w *b, lm2w *q, lm2w *rem) {
  lm2w qq, rr; uint32_t un[LM2W_LIMBS + 1], vn[LM2W_LIMBS];
  uint32_t m = a->n, n = b->n, s = 0u, i; int32_t j;
  if (lm2w_cmp(a, b) < 0) { rr = *a; qq.n = 0u; *q = qq; *rem = rr; return; }
  if (n == 1u) {
    uint64_t k = 0u; uint32_t v = b->d[0];
    for (i = m; i > 0u; i--) { uint64_t cur = (k << 32) | a->d[i - 1u]; qq.d[i - 1u] = (uint32_t)(cur / v); k = cur % v; }
    qq.n = m; lm2w_norm(&qq); lm2w_set(&rr, k); *q = qq; *rem = rr; return;
  }
  { uint32_t top = b->d[n - 1u]; while ((top & 0x80000000u) == 0u) { top <<= 1; s++; } }
  for (i = n - 1u; i > 0u; i--) vn[i] = s ? (b->d[i] << s) | (b->d[i - 1u] >> (32u - s)) : b->d[i];
  vn[0] = b->d[0] << s;
  un[m] = s ? a->d[m - 1u] >> (32u - s) : 0u;
  for (i = m - 1u; i > 0u; i--) un[i] = s ? (a->d[i] << s) | (a->d[i - 1u] >> (32u - s)) : a->d[i];
  un[0] = a->d[0] << s;
  for (j = (int32_t)(m - n); j >= 0; j--) {
    uint64_t num = ((uint64_t)un[j + (int32_t)n] << 32) | un[j + (int32_t)n - 1];
    uint64_t qhat = num / vn[n - 1u], rhat = num % vn[n - 1u];
    int64_t t, k;
    while (qhat >= 0x100000000ULL || qhat * vn[n - 2u] > ((rhat << 32) | un[j + (int32_t)n - 2])) {
      qhat--; rhat += vn[n - 1u];
      if (rhat >= 0x100000000ULL) break;
    }
    k = 0;
    for (i = 0u; i < n; i++) {
      uint64_t p = qhat * vn[i];
      t = (int64_t)un[i + (uint32_t)j] - k - (int64_t)(p & 0xFFFFFFFFu);
      un[i + (uint32_t)j] = (uint32_t)((uint64_t)t & 0xFFFFFFFFu);
      k = (int64_t)(p >> 32) - lm2w_fdiv32(t);
    }
    t = (int64_t)un[j + (int32_t)n] - k; un[j + (int32_t)n] = (uint32_t)((uint64_t)t & 0xFFFFFFFFu);
    qq.d[j] = (uint32_t)qhat;
    if (t < 0) {
      uint64_t c = 0u;
      qq.d[j]--;
      for (i = 0u; i < n; i++) {
        c += (uint64_t)un[i + (uint32_t)j] + vn[i];
        un[i + (uint32_t)j] = (uint32_t)c; c >>= 32;
      }
      un[j + (int32_t)n] += (uint32_t)c;
    }
  }
  qq.n = m - n + 1u; lm2w_norm(&qq);
  for (i = 0u; i < n; i++) rr.d[i] = s ? (un[i] >> s) | (un[i + 1u] << (32u - s)) : un[i];
  rr.n = n; lm2w_norm(&rr);
  *q = qq; *rem = rr;
}
static int lm2w_div(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w q, m;
  if (b->n == 0u) { r->n = 0u; return 0; }
  lm2w_divmod(a, b, &q, &m); *r = q; return 0;
}
static int lm2w_mod(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w q, m;
  if (b->n == 0u) { *r = *a; return 0; }
  lm2w_divmod(a, b, &q, &m); *r = m; return 0;
}
/* a ^ e; for a >= 2 the result has >= e bits, so e > capacity fails */
static int lm2w_pow(const lm2w *a, const lm2w *e, lm2w *r) {
  lm2w acc, base, one; uint64_t k;
  if (e->n == 0u) { lm2w_set(r, 1u); return 0; }
  lm2w_set(&one, 1u);
  if (a->n == 0u || lm2w_cmp(a, &one) == 0) { *r = *a; return 0; }
  if (lm2w_get(e, &k) || k > (uint64_t)LM2W_LIMBS * 32u) return 1;
  acc = one; base = *a;
  for (;;) {
    if (k & 1u) { if (lm2w_mul(&acc, &base, &acc)) return 1; }
    k >>= 1;
    if (k == 0u) break;
    if (lm2w_mul(&base, &base, &base)) return 1;
  }
  *r = acc; return 0;
}
static int lm2w_min(const lm2w *a, const lm2w *b, lm2w *r) { *r = lm2w_cmp(a, b) <= 0 ? *a : *b; return 0; }
static int lm2w_max(const lm2w *a, const lm2w *b, lm2w *r) { *r = lm2w_cmp(a, b) >= 0 ? *a : *b; return 0; }
static int lm2w_gcd(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w x = *a, y = *b, t;
  while (y.n != 0u) { lm2w_mod(&x, &y, &t); x = y; y = t; }
  *r = x; return 0;
}
static int lm2w_lcm(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w g, q;
  if (a->n == 0u || b->n == 0u) { r->n = 0u; return 0; }
  lm2w_gcd(a, b, &g); lm2w_div(a, &g, &q);
  return lm2w_mul(&q, b, r);
}
static int lm2w_fact(const lm2w *n, lm2w *r) {
  lm2w acc, iw; uint64_t k, i;
  if (lm2w_get(n, &k)) return 1;
  lm2w_set(&acc, 1u);
  for (i = 2u; i <= k; i++) { lm2w_set(&iw, i); if (lm2w_mul(&acc, &iw, &acc)) return 1; }
  *r = acc; return 0;
}
/* C(n, k): exact multiplicative formula over min(k, n - k); grows at least 2x per step, so the
 * loop ends by capacity within ~4224 steps */
static int lm2w_choose(const lm2w *n, const lm2w *k, lm2w *r) {
  lm2w c, kk, nk, t, iw;
  uint64_t steps, i;
  if (lm2w_cmp(k, n) > 0) { r->n = 0u; return 0; }
  lm2w_sub(n, k, &nk);
  kk = lm2w_cmp(k, &nk) <= 0 ? *k : nk;
  if (lm2w_get(&kk, &steps)) return 1;
  lm2w_sub(n, &kk, &nk);
  lm2w_set(&c, 1u);
  for (i = 1u; i <= steps; i++) {
    lm2w_set(&iw, i);
    if (lm2w_add(&nk, &iw, &t)) return 1;        /* n - kk + i */
    if (lm2w_mul(&c, &t, &c)) return 1;
    lm2w_div(&c, &iw, &c);                       /* exact */
  }
  *r = c; return 0;
}
/* floor square root by Newton's method from 2^ceil(bits/2) >= sqrt(n) */
static int lm2w_sqrt(const lm2w *n, lm2w *r) {
  lm2w x, y, q, two; uint32_t b = lm2w_bitlen(n), i;
  if (n->n == 0u) { r->n = 0u; return 0; }
  b = (b + 1u) / 2u;
  x.n = b / 32u + 1u;
  for (i = 0u; i < x.n; i++) x.d[i] = 0u;
  x.d[b / 32u] = 1u << (b % 32u);
  lm2w_set(&two, 2u);
  for (;;) {
    lm2w_div(n, &x, &q);
    if (lm2w_add(&x, &q, &y)) return 1;
    lm2w_div(&y, &two, &y);
    if (lm2w_cmp(&y, &x) >= 0) break;
    x = y;
  }
  *r = x; return 0;
}
/* builtins whose reference evaluation is budgeted to small arguments: 64-bit only */
static int lm2w_minfac(const lm2w *n, lm2w *r) {
  uint64_t x, m; if (lm2w_get(n, &x)) return 1;
  lm2_minfac(x, &m); lm2w_set(r, m); return 0;
}
static int lm2w_prime(const lm2w *n, lm2w *r) {
  uint64_t x; if (lm2w_get(n, &x)) return 1;
  lm2w_set(r, lm2_isprime(x)); return 0;
}
static int lm2w_bigomega(const lm2w *n, lm2w *r) {
  uint64_t x; if (lm2w_get(n, &x)) return 1;
  lm2w_set(r, lm2_bigomega(x)); return 0;
}
static int lm2w_dvd(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w m;
  if (a->n == 0u) { lm2w_set(r, b->n == 0u ? 1u : 0u); return 0; }
  lm2w_mod(b, a, &m); lm2w_set(r, m.n == 0u ? 1u : 0u); return 0;
}
static int lm2w_fib(const lm2w *n, lm2w *r) {
  lm2w x, y, z; uint64_t k, i;
  if (lm2w_get(n, &k)) return 1;
  lm2w_set(&x, 0u); lm2w_set(&y, 1u);
  for (i = 0u; i < k; i++) {
    if (lm2w_add(&x, &y, &z)) { if (i + 1u == k) { *r = y; return 0; } return 1; }
    x = y; y = z;
  }
  *r = x; return 0;
}
static int lm2w_log(const lm2w *b, const lm2w *n, lm2w *r) {
  lm2w m = *n, one; uint64_t k = 0u;
  lm2w_set(&one, 1u);
  if (lm2w_cmp(b, &one) <= 0) { r->n = 0u; return 0; }
  while (lm2w_cmp(&m, b) >= 0) { lm2w_div(&m, b, &m); k++; }
  lm2w_set(r, k); return 0;
}
static int lm2w_log2(const lm2w *n, lm2w *r) {
  uint32_t b = lm2w_bitlen(n); lm2w_set(r, b > 0u ? b - 1u : 0u); return 0;
}
static int lm2w_padic(const lm2w *p, const lm2w *n, lm2w *r) {
  lm2w m = *n, q, rem, one; uint64_t k = 0u;
  lm2w_set(&one, 1u);
  if (lm2w_cmp(p, &one) <= 0 || n->n == 0u) { r->n = 0u; return 0; }
  for (;;) { lm2w_divmod(&m, p, &q, &rem); if (rem.n != 0u) break; m = q; k++; }
  lm2w_set(r, k); return 0;
}
static int lm2w_digsum(const lm2w *b, const lm2w *n, lm2w *r) {
  lm2w m = *n, q, d, s, one;
  lm2w_set(&one, 1u);
  if (lm2w_cmp(b, &one) <= 0) { *r = *n; return 0; }
  s.n = 0u;
  while (m.n != 0u) { lm2w_divmod(&m, b, &q, &d); if (lm2w_add(&s, &d, &s)) return 1; m = q; }
  *r = s; return 0;
}
static int lm2w_diglen(const lm2w *b, const lm2w *n, lm2w *r) {
  lm2w m = *n, q, d, one; uint64_t k = 0u;
  lm2w_set(&one, 1u);
  if (b->n == 0u) { lm2w_set(r, n->n == 0u ? 0u : 1u); return 0; }
  if (lm2w_cmp(b, &one) == 0) { *r = *n; return 0; }
  while (m.n != 0u) { lm2w_divmod(&m, b, &q, &d); m = q; k++; }
  lm2w_set(r, k); return 0;
}
static int lm2w_digrev(const lm2w *b, const lm2w *n, lm2w *r) {
  lm2w m = *n, q, d, acc, one;
  lm2w_set(&one, 1u);
  if (lm2w_cmp(b, &one) <= 0) { *r = *n; return 0; }
  acc.n = 0u;
  while (m.n != 0u) {
    lm2w_divmod(&m, b, &q, &d);
    if (lm2w_mul(&acc, b, &acc) || lm2w_add(&acc, &d, &acc)) return 1;
    m = q;
  }
  *r = acc; return 0;
}

static int lm2w_xor(const lm2w *a, const lm2w *b, lm2w *r) {
  lm2w t; uint32_t i, m = a->n > b->n ? a->n : b->n;
  for (i = 0u; i < m; i++) t.d[i] = (i < a->n ? a->d[i] : 0u) ^ (i < b->n ? b->d[i] : 0u);
  t.n = m; lm2w_norm(&t); *r = t; return 0;
}
/* ---- ℤ (sign-magnitude) ---- */
static void lm2wi_fix(lm2wi *a) { if (a->m.n == 0u) a->neg = 0; }
static int lm2wi_ofnat(const lm2w *a, lm2wi *r) { r->m = *a; r->neg = 0; return 0; }
static int lm2wi_neg(const lm2wi *a, lm2wi *r) { lm2wi t = *a; t.neg = !t.neg; lm2wi_fix(&t); *r = t; return 0; }
static int lm2wi_sign(const lm2wi *a, lm2wi *r) {
  lm2wi t; lm2w_set(&t.m, a->m.n == 0u ? 0u : 1u); t.neg = a->neg; lm2wi_fix(&t); *r = t; return 0;
}
static int lm2wi_add(const lm2wi *a, const lm2wi *b, lm2wi *r) {
  lm2wi t;
  if (a->neg == b->neg) { if (lm2w_add(&a->m, &b->m, &t.m)) return 1; t.neg = a->neg; }
  else if (lm2w_cmp(&a->m, &b->m) >= 0) { lm2w_sub(&a->m, &b->m, &t.m); t.neg = a->neg; }
  else { lm2w_sub(&b->m, &a->m, &t.m); t.neg = b->neg; }
  lm2wi_fix(&t); *r = t; return 0;
}
static int lm2wi_sub(const lm2wi *a, const lm2wi *b, lm2wi *r) {
  lm2wi nb = *b; nb.neg = !nb.neg; lm2wi_fix(&nb); return lm2wi_add(a, &nb, r);
}
static int lm2wi_mul(const lm2wi *a, const lm2wi *b, lm2wi *r) {
  lm2wi t; if (lm2w_mul(&a->m, &b->m, &t.m)) return 1;
  t.neg = a->neg != b->neg; lm2wi_fix(&t); *r = t; return 0;
}
static int lm2wi_pow(const lm2wi *a, const lm2w *e, lm2wi *r) {
  lm2wi t; if (lm2w_pow(&a->m, e, &t.m)) return 1;
  t.neg = a->neg && e->n != 0u && (e->d[0] & 1u); lm2wi_fix(&t); *r = t; return 0;
}
static int lm2wi_tonat(const lm2wi *a, lm2w *r) { if (a->neg) r->n = 0u; else *r = a->m; return 0; }
static int lm2wi_natabs(const lm2wi *a, lm2w *r) { *r = a->m; return 0; }
static int lm2wi_cmp(const lm2wi *a, const lm2wi *b) {
  if (a->neg != b->neg) return a->neg ? -1 : 1;
  return a->neg ? -lm2w_cmp(&a->m, &b->m) : lm2w_cmp(&a->m, &b->m);
}

/* ---- ℚ (MathIR v6): normalized fraction num / den, den > 0, gcd(|num|, den) = 1, 0 = 0/1.
 * Lean semantics: x / 0 = 0, 0⁻¹ = 0. ℚ subterms are evaluated only on this exact path. ---- */
typedef struct { lm2wi num; lm2w den; } lm2wq;

static int lm2wq_norm(lm2wq *q) {
  lm2w g, one;
  if (q->den.n == 0u) return 1;                  /* never produced; fail closed */
  lm2w_set(&one, 1u);
  if (q->num.m.n == 0u) { q->num.neg = 0; q->den = one; return 0; }
  lm2w_gcd(&q->num.m, &q->den, &g);
  if (lm2w_cmp(&g, &one) != 0) { lm2w_div(&q->num.m, &g, &q->num.m); lm2w_div(&q->den, &g, &q->den); }
  return 0;
}
static int lm2wq_ofnat(const lm2w *a, lm2wq *r) { lm2wq t; t.num.m = *a; t.num.neg = 0; lm2w_set(&t.den, 1u); lm2wi_fix(&t.num); *r = t; return 0; }
static int lm2wq_ofint(const lm2wi *a, lm2wq *r) { lm2wq t; t.num = *a; lm2w_set(&t.den, 1u); *r = t; return 0; }
static int lm2wq_add(const lm2wq *a, const lm2wq *b, lm2wq *r) {
  lm2wq t; lm2wi x, y; lm2wi ad, bd;
  ad.neg = 0; ad.m = a->den; bd.neg = 0; bd.m = b->den;
  if (lm2wi_mul(&a->num, &bd, &x) || lm2wi_mul(&b->num, &ad, &y) || lm2wi_add(&x, &y, &t.num)) return 1;
  if (lm2w_mul(&a->den, &b->den, &t.den)) return 1;
  if (lm2wq_norm(&t)) return 1;
  *r = t; return 0;
}
static int lm2wq_neg(const lm2wq *a, lm2wq *r) { lm2wq t = *a; t.num.neg = !t.num.neg; lm2wi_fix(&t.num); *r = t; return 0; }
static int lm2wq_sub(const lm2wq *a, const lm2wq *b, lm2wq *r) { lm2wq nb; lm2wq_neg(b, &nb); return lm2wq_add(a, &nb, r); }
static int lm2wq_mul(const lm2wq *a, const lm2wq *b, lm2wq *r) {
  lm2wq t;
  if (lm2wi_mul(&a->num, &b->num, &t.num) || lm2w_mul(&a->den, &b->den, &t.den)) return 1;
  if (lm2wq_norm(&t)) return 1;
  *r = t; return 0;
}
static int lm2wq_inv(const lm2wq *a, lm2wq *r) {
  lm2wq t;
  if (a->num.m.n == 0u) { lm2w zero; zero.n = 0u; return lm2wq_ofnat(&zero, r); }
  t.num.m = a->den; t.num.neg = a->num.neg; t.den = a->num.m;
  *r = t; return 0;                              /* already coprime */
}
static int lm2wq_div(const lm2wq *a, const lm2wq *b, lm2wq *r) { lm2wq ib; lm2wq_inv(b, &ib); return lm2wq_mul(a, &ib, r); }
static int lm2wq_pow(const lm2wq *a, const lm2w *e, lm2wq *r) {
  lm2wq t;                                       /* num^e / den^e stays coprime */
  if (lm2wi_pow(&a->num, e, &t.num) || lm2w_pow(&a->den, e, &t.den)) return 1;
  *r = t; return 0;
}
static int lm2wq_num(const lm2wq *a, lm2wi *r) { *r = a->num; return 0; }
static int lm2wq_den(const lm2wq *a, lm2w *r) { *r = a->den; return 0; }
static int lm2wq_cmp(const lm2wq *a, const lm2wq *b) {   /* sign of a.num*b.den - b.num*a.den */
  lm2wi x, y, ad, bd; ad.neg = 0; ad.m = a->den; bd.neg = 0; bd.m = b->den;
  if (lm2wi_mul(&a->num, &bd, &x) || lm2wi_mul(&b->num, &ad, &y)) return 2;   /* 2 = unknown: caller fails */
  return lm2wi_cmp(&x, &y);
}
#endif
