/* { dg-do compile } */
/* { dg-options "-O3 -march=rv32imc_xcvsimd -mabi=ilp32" } */

typedef _Complex short cshort;

void
add_conj (cshort *c, cshort *a, cshort *b, int n) {
for (int i = 0; i < n; i++)
  c[i] = a[i] + ~b[i];
}

/* { dg-final { scan-assembler "cv\\.cplxconj" } } */
/* { dg-final { scan-assembler "cv\\.add\\.h" } } */
/* { dg-final { scan-assembler-not "cv\\.shuffle2\\.h" } } */
/* { dg-final { scan-assembler-not "cv\\.insert\\.h" } } */