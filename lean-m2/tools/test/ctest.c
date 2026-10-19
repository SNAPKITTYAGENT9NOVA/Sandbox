/* SPDX-License-Identifier: AGPL-3.0-only */
/* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) */
/* build.sh: run every Lean reference case through the generated C (gcc build). */
#include <stdio.h>
#include <stdint.h>
#include "lm2_gen.h"
uint32_t lm2_gen_case_count(void);
int32_t lm2_gen_case_get(uint32_t, uint32_t*, uint64_t*, uint64_t*, uint64_t*, int32_t*, uint64_t*);
int main(void) {
  uint32_t n = lm2_gen_case_count(), i, f, bad = 0, inc = 0;
  for (i = 0; i < n; i++) {
    uint64_t a0, a1, a2, v, out = 0; int32_t st;
    lm2_gen_case_get(i, &f, &a0, &a1, &a2, &st, &v);
    int32_t r = lm2_gen_call(f, a0, a1, a2, &out);
    if (st == 0 && r == 0 && out != v) { bad++; if (bad < 5) printf("WRONG fn=%u (%llu,%llu,%llu) want %llu got %llu\n", f, (unsigned long long)a0, (unsigned long long)a1, (unsigned long long)a2, (unsigned long long)v, (unsigned long long)out); }
    else if (st == 0 && r != 0) inc++;          /* Lean value fits, generated code gave up */
    else if (st != 0 && r == 0) bad++;          /* Lean value overflows, generated code claimed a value */
  }
  printf("C cases=%u unsound=%u incomplete=%u\n", n, bad, inc);
  return bad || inc;
}
