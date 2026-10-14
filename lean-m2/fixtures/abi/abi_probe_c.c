/* LEAN-M2-CC-001 ABI fixture. Compiled ONLY by ccomp (CompCert).
 * C99, fixed-width scalars, caller-owned buffers with explicit lengths,
 * no struct/union passed or returned by value (CompCert AArch64 ABI restriction). */
#include <stdint.h>
#include <stddef.h>

int64_t cc_add64(int64_t a, int64_t b) { return a + b; }

/* Returns 0 on success, -1 if buf or out is NULL (error-return convention). */
int32_t cc_sum_buf(const int64_t *buf, uint64_t len, int64_t *out) {
  if (buf == NULL || out == NULL) return -1;
  int64_t s = 0;
  for (uint64_t i = 0; i < len; i++) s += buf[i];
  *out = s;
  return 0;
}

/* C -> Modula-2 direction: call a Modula-2 procedure through a function pointer.
 * Avoids depending on gm2's exported-symbol mangling. */
int64_t cc_apply(int64_t (*f)(int64_t, int64_t), int64_t a, int64_t b) {
  return f(a, b);
}
