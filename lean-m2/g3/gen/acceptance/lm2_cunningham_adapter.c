/* SPDX-License-Identifier: AGPL-3.0-only */
/* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) */
/* Acceptance adapter (hand-written, thin): exposes the GENERATED firstKindTerm under the symbol
 * SLICE-001's driver links against, so the generator is judged by SLICE-001's own 2,511 cases. */
#include "lm2_gen.h"

int32_t lm2_cunningham_first_kind_term(uint64_t p, uint64_t n, uint64_t *out)
{
  if (out == 0) return LM2_ERR_NULL;
  return lm2_CunninghamChain_firstKindTerm(p, n, out);
}
