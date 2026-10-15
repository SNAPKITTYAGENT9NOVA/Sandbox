/* LEAN-M2-CC-001 SLICE-001. Compiled ONLY by CompCert (ccomp), C99 subset.
 *
 * Lean source (formal-conjectures @ 84cf7f8, CunninghamChain.lean):
 *   def firstKindTerm (p : N) : N -> N
 *     | 0     => p
 *     | n + 1 => 2 * firstKindTerm p n + 1
 *
 * Machine semantics: exact value when it fits in 64 bits, otherwise LM2_OVERFLOW (never wraps).
 * Facts used, proved in Spec.lean:
 *   overflow_of_ge_65 : 65 <= n -> 2^64 - 1 < firstKindTerm p n   (short-circuit below)
 *   each step t -> 2t + 1 fits iff t <= (UINT64_MAX - 1) / 2      (guard below)
 * Hence the loop runs at most 64 iterations for every input. */
#include "lm2_cunningham.h"

int32_t lm2_cunningham_first_kind_term(uint64_t p, uint64_t n, uint64_t *out)
{
  uint64_t t;
  uint64_t i;
  if (out == 0) {
    return LM2_ERR_NULL;
  }
  if (n >= 65u) {
    return LM2_OVERFLOW;
  }
  t = p;
  for (i = 0u; i < n; i++) {
    if (t > (UINT64_MAX - 1u) / 2u) {
      return LM2_OVERFLOW;
    }
    t = 2u * t + 1u;
  }
  *out = t;
  return LM2_OK;
}
