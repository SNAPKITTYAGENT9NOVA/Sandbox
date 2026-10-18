/* SPDX-License-Identifier: AGPL-3.0-only */
/* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) */
/* LEAN-M2-CC-001 SLICE-001: CunninghamChain.firstKindTerm on 64-bit unsigned integers.
 * Semantic contract: lean-m2/g3/SLICE-001-firstKindTerm.md. ABI: scalars + caller-owned
 * out-pointer only (no aggregates by value), AAPCS64. */
#ifndef LM2_CUNNINGHAM_H
#define LM2_CUNNINGHAM_H
#include <stdint.h>

#define LM2_OK        0   /* *out = firstKindTerm(p, n)                         */
#define LM2_OVERFLOW  1   /* result > UINT64_MAX; *out is NOT written           */
#define LM2_ERR_NULL (-1) /* out == NULL                                        */

int32_t lm2_cunningham_first_kind_term(uint64_t p, uint64_t n, uint64_t *out);

#endif
