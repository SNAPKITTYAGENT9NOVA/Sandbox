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
#endif
