/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

typedef signed char v4qi __attribute__ ((vector_size (4)));
typedef short v2hi __attribute__ ((vector_size (4)));

void
perm1_b (v4qi *c, v4qi *a, v4qi *m) {
  *c = __builtin_shuffle (*a, *m);
}

void
perm1_h (v2hi *c, v2hi *a, v2hi *m) {
  *c = __builtin_shuffle (*a, *m);
}

void
perm2_b (v4qi *c, v4qi *a, v4qi *b, v4qi *m) {
  *c = __builtin_shuffle (*a, *b, *m);
}

void
perm2_h (v2hi *c, v2hi *a, v2hi *b, v2hi *m) {
  *c = __builtin_shuffle (*a, *b, *m);
}

/* { dg-final { scan-assembler "cv\\.shuffle\\.b" } } */
/* { dg-final { scan-assembler "cv\\.shuffle\\.h" } } */
/* { dg-final { scan-assembler "cv\\.shuffle2\\.b" } } */
/* { dg-final { scan-assembler "cv\\.shuffle2\\.h" } } */
