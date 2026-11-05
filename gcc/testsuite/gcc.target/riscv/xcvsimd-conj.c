/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

typedef _Complex short cshort;

void
neg_b (signed char *c, signed char *a, int n) {
for (int i = 0; i < n; i++)
  c[i] = -a[i];
}

void
conj_c (cshort *c, cshort *a, int n) {
for (int i = 0; i < n; i++)
  c[i] = ~a[i];
}

/* { dg-final { scan-assembler "cv\\.sub\\.b\\s+\\w+,zero," } } */
/* { dg-final { scan-assembler "cv\\.sub\\.h\\s+\\w+,zero," } } */